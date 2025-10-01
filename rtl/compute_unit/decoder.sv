// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "bgpu.svh"

/// Decoder
module decoder import bgpu_pkg::*; #(
    /// Width of the Program Counter
    parameter int unsigned PcWidth = 32,
    /// Number of warps per compute unit
    parameter int unsigned NumWarps = 8,
    /// Number of threads per warp
    parameter int unsigned WarpWidth = 32,
    /// Encoded instruction width
    parameter int unsigned EncInstWidth = 32,
    /// How many registers can each warp access as operand or destination
    parameter int unsigned RegIdxWidth = 8,
    /// How many operands each instruction can have
    parameter int unsigned OperandsPerInst = 2,

    /// Dependent parameter, do **not** overwrite.
    parameter int unsigned SubwarpIdWidth = WarpWidth > 1 ? $clog2(WarpWidth) : 1,
    parameter int unsigned WidWidth       = NumWarps > 1  ? $clog2(NumWarps)  : 1,
    parameter type         wid_t          = logic [      WidWidth-1:0],
    parameter type         reg_idx_t      = logic [   RegIdxWidth-1:0],
    parameter type         pc_t           = logic [       PcWidth-1:0],
    parameter type         act_mask_t     = logic [     WarpWidth-1:0],
    parameter type         enc_inst_t     = logic [  EncInstWidth-1:0],
    parameter type         subwarp_id_t   = logic [SubwarpIdWidth-1:0]
) (
    // From Instruction Cache
    output logic        dec_ready_o,
    input  logic        ic_valid_i,
    input  pc_t         ic_pc_i,
    input  act_mask_t   ic_act_mask_i,
    input  wid_t        ic_warp_id_i,
    input  subwarp_id_t ic_subwarp_id_i,
    input  enc_inst_t   ic_inst_i,

    // To Dispatcher
    input  logic        disp_ready_i,
    output logic        dec_valid_o,
    output pc_t         dec_pc_o,
    output act_mask_t   dec_act_mask_o,
    output wid_t        dec_warp_id_o,
    output subwarp_id_t dec_subwarp_id_o,
    output inst_t       dec_inst_o,
    output reg_idx_t    dec_dst_o,
    output logic        [OperandsPerInst-1:0] dec_operands_required_o,
    output reg_idx_t    [OperandsPerInst-1:0] dec_operands_o,

    // To Fetcher |-> tells it what the next PC is
    output logic        dec_decoded_o,
    output logic        dec_decoded_control_o,
    output logic        dec_stop_warp_o,
    output logic        dec_decoded_branch_o,
    output logic        dec_decoded_sync_o,
    output wid_t        dec_decoded_warp_id_o,
    output subwarp_id_t dec_decoded_subwarp_id_o,
    output pc_t         dec_decoded_next_pc_o
);
    // Pass through signals
    assign dec_ready_o       = disp_ready_i;
    assign dec_pc_o          = ic_pc_i;
    assign dec_act_mask_o    = ic_act_mask_i;
    assign dec_warp_id_o     = ic_warp_id_i;
    assign dec_subwarp_id_o  = ic_subwarp_id_i;
    assign dec_inst_o        = inst_t'(ic_inst_i[31:24]);
    assign dec_dst_o         = ic_inst_i[23:16];
    assign dec_operands_o[1] = ic_inst_i[15:8];
    assign dec_operands_o[0] = ic_inst_i[7:0];

    // Instruction was decoded if a handshake between Decoder and Dispatcher happend
    assign dec_decoded_o            = ((ic_valid_i && dec_decoded_control_o) || dec_valid_o)
                                    && disp_ready_i;
    assign dec_decoded_warp_id_o    = dec_warp_id_o;
    assign dec_decoded_subwarp_id_o = ic_subwarp_id_i;

    // Stop the warp if the instruction is a stop instruction
    assign dec_stop_warp_o = ic_inst_i[31:24] == '1;

    // Control instructions are not sent to the Dispatcher
    assign dec_valid_o       = ic_valid_i && (!dec_decoded_control_o);

    // Decode instruction
    always_comb begin : decode
        // By default, increment the PC by one
        dec_decoded_next_pc_o = dec_pc_o + 'd1;
        dec_decoded_branch_o  = 1'b0;
        dec_decoded_sync_o    = 1'b0;

        // By default, all operands are immediate values
        dec_operands_required_o = '0;

        // Stop is a control instruction
        dec_decoded_control_o = dec_stop_warp_o;

        // Integer Unit
        if (dec_inst_o.eu == EU_IU) begin : decode_iu
            // Two register operands
            if (dec_inst_o.subtype inside {
                IU_ADD, IU_SUB, IU_AND, IU_OR, IU_XOR, IU_SHL
            })
                dec_operands_required_o = '1;

            // First operand is an immediate, second is a register
            if (dec_inst_o.subtype inside {
                IU_ADDI, IU_SUBI, IU_SHLI
            }) begin
                dec_operands_required_o[0] = 1'b0;
                dec_operands_required_o[1] = 1'b1;
            end
        end : decode_iu

        // Floating Point Unit
        else if (dec_inst_o.eu == EU_FPU) begin : decode_fpu
            dec_operands_required_o = '1;

            // Only one register operand
            if (dec_inst_o.subtype inside {
                FPU_INT_TO_FP, FPU_FP_TO_INT
            })
                dec_operands_required_o[1] = 1'b0;
        end : decode_fpu

        // Load Store Unit
        else if (dec_inst_o.eu == EU_LSU) begin : decode_lsu
            // LSU instructions always have two operands register operands
            // Operand 1 is the address
            // Operand 0 is the data to store
            dec_operands_required_o[0] = dec_inst_o.subtype inside `INST_STORE; // Data
            dec_operands_required_o[1] = 1'b1; // Address
        end : decode_lsu

        // Branch Unit
        else if (dec_inst_o.eu == EU_BRU) begin : decode_bru
            if (dec_inst_o.subtype == BRU_JMP) begin : jump_instruction
                // Both operands are immediate values forming the offset

                // Sign extend the offset and add it to the PC
                if (PcWidth > 16)
                    dec_decoded_next_pc_o = dec_pc_o
                        + {{(PcWidth-16){ic_inst_i[15]}}, ic_inst_i[15:0]} + 'd1;
                else
                    dec_decoded_next_pc_o = dec_pc_o + ic_inst_i[PcWidth-1:0] + 'd1;

                // Is a control instruction
                dec_decoded_control_o = 1'b1;
            end : jump_instruction
            else if (dec_inst_o.subtype == BRU_SYNC) begin : sync_instruction
                dec_decoded_control_o = 1'b1;
                dec_decoded_sync_o    = 1'b1;
            end : sync_instruction
            else begin : branch_instruction
                // Op1 is an immediate value holding the offset
                // Op2 is a register holding the condition
                dec_operands_required_o[0] = 1'b0; // Immediate value
                dec_operands_required_o[1] = 1'b1; // Register Operand

                dec_decoded_branch_o = 1'b1;
            end : branch_instruction
        end : decode_bru
    end

    `ifndef SYNTHESIS
        initial assert (EncInstWidth == 32)
            else $fatal(1, "EncInstWidth must be 32 bits, got %0d", EncInstWidth);

        initial assert (RegIdxWidth == 8)
            else $fatal(1, "RegIdxWidth must be 8 bits, got %0d", RegIdxWidth);

        initial assert (OperandsPerInst == 2)
            else $fatal(1, "OperandsPerInst must be 2, got %0d", OperandsPerInst);
    `endif
endmodule : decoder
