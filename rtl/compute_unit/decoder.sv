// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "bgpu/instructions.svh"

/// Decoder
module decoder #(
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
    parameter int unsigned WidWidth   = NumWarps > 1 ? $clog2(NumWarps) : 1,
    parameter type         wid_t      = logic [    WidWidth-1:0],
    parameter type         reg_idx_t  = logic [ RegIdxWidth-1:0],
    parameter type         pc_t       = logic [     PcWidth-1:0],
    parameter type         act_mask_t = logic [   WarpWidth-1:0],
    parameter type         enc_inst_t = logic [EncInstWidth-1:0]
) (
    // From Instruction Cache
    output logic      dec_ready_o,
    input  logic      ic_valid_i,
    input  pc_t       ic_pc_i,
    input  act_mask_t ic_act_mask_i,
    input  wid_t      ic_warp_id_i,
    input  enc_inst_t ic_inst_i,

    // To Dispatcher
    input  logic       disp_ready_i,
    output logic       dec_valid_o,
    output pc_t        dec_pc_o,
    output act_mask_t  dec_act_mask_o,
    output wid_t       dec_warp_id_o,
    output bgpu_inst_t dec_inst_o,
    output reg_idx_t   dec_dst_o,
    output logic       [OperandsPerInst-1:0] dec_operands_required_o,
    output reg_idx_t   [OperandsPerInst-1:0] dec_operands_o,

    // To Fetcher |-> tells it what the next PC is
    output logic dec_decoded_o,
    output logic dec_stop_warp_o,
    output wid_t dec_decoded_warp_id_o,
    output pc_t  dec_decoded_next_pc_o
);
    // Pass through signals
    assign dec_ready_o    = disp_ready_i;
    assign dec_pc_o       = ic_pc_i;
    assign dec_act_mask_o = ic_act_mask_i;
    assign dec_warp_id_o  = ic_warp_id_i;

    // Instruction was decoded if a handshake between Decoder and Dispatcher happend
    assign dec_decoded_o         = ic_valid_i && dec_stop_warp_o || dec_valid_o && disp_ready_i;
    assign dec_decoded_warp_id_o = dec_warp_id_o;
    assign dec_decoded_next_pc_o = dec_pc_o + 'd1;

    assign dec_stop_warp_o = ic_inst_i[31:24] == '1;

    // Decode instruction
    always_comb begin : decode
        // Default
        dec_valid_o       = ic_valid_i && !dec_stop_warp_o;
        dec_inst_o        = bgpu_inst_t'(ic_inst_i[31:24]);
        dec_dst_o         = ic_inst_i[23:16];

        dec_operands_required_o = '0;
        if(dec_inst_o.eu == BGPU_INST_TYPE_IU) begin : decode_iu
            // Two register operands
            if (dec_inst_o.subtype inside `BGPU_IU_TWO_REG_OPERANDS)
                dec_operands_required_o = '1;

            // First operand is a register, second is an immediate value (register index)
            if (dec_inst_o.subtype inside `BGPU_IU_REG_IMM_OPERANDS) begin
                dec_operands_required_o[0] = 1'b1;
                dec_operands_required_o[1] = 1'b0;
            end
        end : decode_iu
        else if (dec_inst_o.eu == BGPU_INST_TYPE_LSU) begin : decode_lsu
            // LSU instructions always have two operands register operands
            // Operand 0 is the address
            // Operand 1 is the data to store
            dec_operands_required_o[0] = 1'b1;
            dec_operands_required_o[1] = 1'b1;
        end : decode_lsu

        dec_operands_o[0] = ic_inst_i[15:8];
        dec_operands_o[1] = ic_inst_i[7:0];
    end

    `ifndef SYNTHESIS
        initial assert (EncInstWidth == 32)
            else $fatal("EncInstWidth must be 32 bits, got %0d", EncInstWidth);

        initial assert (RegIdxWidth == 8)
            else $fatal("RegIdxWidth must be 8 bits, got %0d", RegIdxWidth);

        initial assert (OperandsPerInst == 2)
            else $fatal("OperandsPerInst must be 2, got %0d", OperandsPerInst);
    `endif
endmodule : decoder
