// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "common_cells/registers.svh"

/// Operand Collector
module operand_collector #(
    /// Number of inflight instructions per warp
    parameter int unsigned NumTags = 8,
    /// Width of the Program Counter
    parameter int unsigned PcWidth = 32,
    /// Number of warps per compute unit
    parameter int unsigned NumWarps = 8,
    /// Number of threads per warp
    parameter int unsigned WarpWidth = 32,
    /// How many registers can each warp access as operand or destination
    parameter int unsigned RegIdxWidth = 6,
    /// How many operands each instruction can have
    parameter int unsigned OperandsPerInst = 2,
    /// Width of a singled register
    parameter int unsigned RegWidth = 32,

    /// Dependent parameter, do **not** overwrite.
    parameter int unsigned TagWidth    = $clog2(NumTags),
    parameter int unsigned WidWidth    = NumWarps > 1 ? $clog2(NumWarps) : 1,
    parameter type         wid_t       = logic [            WidWidth-1:0],
    parameter type         reg_idx_t   = logic [         RegIdxWidth-1:0],
    parameter type         pc_t        = logic [             PcWidth-1:0],
    parameter type         act_mask_t  = logic [           WarpWidth-1:0],
    parameter type         warp_data_t = logic [RegWidth * WarpWidth-1:0],
    parameter type         iid_t       = logic [   TagWidth+WidWidth-1:0]
) (
    // Clock and Reset
    input  logic clk_i,
    input  logic rst_ni,

    /// From Multi Warp Dispatcher
    output logic      opc_ready_o,
    input  logic      disp_valid_i,
    input  iid_t      disp_tag_i,
    input  pc_t       disp_pc_i,
    input  act_mask_t disp_act_mask_i,
    input  reg_idx_t  disp_dst_i,
    input  reg_idx_t  [OperandsPerInst-1:0] disp_src_i,

    /// To Register File
    output logic     [OperandsPerInst-1:0] opc_read_req_valid_o,
    output wid_t     [OperandsPerInst-1:0] opc_read_req_wid_o,
    output reg_idx_t [OperandsPerInst-1:0] opc_read_req_reg_idx_o,
    input  logic     [OperandsPerInst-1:0] opc_read_req_ready_i,

    /// From Register File
    input  logic       [OperandsPerInst-1:0] opc_read_rsp_valid_i,
    input  warp_data_t [OperandsPerInst-1:0] opc_read_rsp_data_i,


    /// To Execution Units
    input  logic       eu_ready_i,
    output logic       opc_valid_o,
    output iid_t       opc_tag_o,
    output pc_t        opc_pc_o,
    output act_mask_t  opc_act_mask_o,
    output reg_idx_t   opc_dst_o,
    output warp_data_t [OperandsPerInst-1:0] opc_operand_data_o
);
    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Do we have a valid instruction?
    logic occupied_q, occupied_d;
    // Instruction Tag
    iid_t tag_q, tag_d;
    // Instruction Program Counter
    pc_t pc_q, pc_d;
    // Instruction Activate Mask
    act_mask_t act_mask_q, act_mask_d;
    // Instruction Destination Register Index
    reg_idx_t dst_q, dst_d;
    // Have we already sent a request for the operands?
    logic [OperandsPerInst-1:0] operand_requested_q, operand_requested_d;
    // Are the operands ready?
    logic [OperandsPerInst-1:0] operand_ready_q, operand_ready_d;
    // Operands Register Indecies
    reg_idx_t [OperandsPerInst-1:0] operand_reg_idx_q, operand_reg_idx_d;
    // Operands Data
    warp_data_t [OperandsPerInst-1:0] operand_data_q, operand_data_d;

    // ########################################################################################
    // # Sequential Logic                                                                    #
    // ########################################################################################

    // Operand Request Logic
    for (genvar i = 0; i < OperandsPerInst; i++) begin : gen_operand_request
        always_comb begin : operand_request_logic
            // Default Register Data
            operand_requested_d[i] = operand_requested_q[i];
            operand_ready_d    [i] = operand_ready_q[i];
            operand_reg_idx_d  [i] = operand_reg_idx_q[i];
            operand_data_d     [i] = operand_data_q[i];

            // Default Outputs |-> make request
            opc_read_req_valid_o  [i] = !operand_requested_q[i] && occupied_q;
            opc_read_req_wid_o    [i] = tag_q[WidWidth-1:0];
            opc_read_req_reg_idx_o[i] = operand_reg_idx_q[i];

            // Request handshake
            if (opc_read_req_valid_o[i] && opc_read_req_ready_i[i]) begin : request_handshake
                // We have requested the operand
                operand_requested_d[i] = 1'b1;
            end : request_handshake

            // Receiveing the operand data
            if (opc_read_rsp_valid_i[i]) begin : receive_operand_data
                // We have received the operand data
                operand_ready_d[i] = 1'b1;
                operand_data_d [i] = opc_read_rsp_data_i[i];
            end : receive_operand_data

            // Insert new instruction |-> Handshake
            if (disp_valid_i && opc_ready_o) begin : new_instruction
                operand_requested_d[i] = 1'b0;
                operand_ready_d    [i] = 1'b0;
                operand_reg_idx_d  [i] = disp_src_i[i];
            end : new_instruction
        end : operand_request_logic
    end : gen_operand_request

    // Instruction Logic
    always_comb begin : instruction_logic
        // Default Register Data
        occupied_d = occupied_q;
        tag_d      = tag_q;
        pc_d       = pc_q;
        act_mask_d = act_mask_q;
        dst_d      = dst_q;

        // Insert new instruction |-> Handshake
        if (disp_valid_i && opc_ready_o) begin : new_instruction
            occupied_d = 1'b1;
            tag_d      = disp_tag_i;
            pc_d       = disp_pc_i;
            act_mask_d = disp_act_mask_i;
            dst_d      = disp_dst_i;
        end : new_instruction

        // Output Handshake
        if (eu_ready_i && opc_valid_o) begin : output_handshake
            occupied_d = 1'b0; // We are no longer occupied
        end : output_handshake

    end : instruction_logic

    // We are ready to accept a new instruction if we are not occupied
    assign opc_ready_o = !occupied_q;

    // Outputs to Execution Units
    assign opc_valid_o        = occupied_q && &operand_ready_q;
    assign opc_tag_o          = tag_q;
    assign opc_pc_o           = pc_q;
    assign opc_act_mask_o     = act_mask_q;
    assign opc_dst_o          = dst_q;
    assign opc_operand_data_o = operand_data_q;

    // ########################################################################################
    // # Sequential Logic                                                                     #
    // ########################################################################################

    // Common
    `FF(occupied_q, occupied_d, '0, clk_i, rst_ni);
    `FF(tag_q,      tag_d,      '0, clk_i, rst_ni);
    `FF(pc_q,       pc_d,       '0, clk_i, rst_ni);
    `FF(act_mask_q, act_mask_d, '0, clk_i, rst_ni);
    `FF(dst_q,      dst_d,      '0, clk_i, rst_ni);

    // Operands
    for (genvar i = 0; i < OperandsPerInst; i++) begin : gen_operand_ff
        `FF(operand_requested_q[i], operand_requested_d[i], '0, clk_i, rst_ni);
        `FF(operand_ready_q    [i], operand_ready_d    [i], '0, clk_i, rst_ni);
        `FF(operand_reg_idx_q  [i], operand_reg_idx_d  [i], '0, clk_i, rst_ni);
        `FF(operand_data_q     [i], operand_data_d     [i], '0, clk_i, rst_ni);
    end : gen_operand_ff

    // ########################################################################################
    // # Assertions                                                                           #
    // ########################################################################################

    // Operands
    `ifndef SYNTHESIS
        for (genvar i = 0; i < OperandsPerInst; i++) begin : gen_operand_assertions
            // Assert that we do not request an operand if we are not occupied
            assert property (@(posedge clk_i) !occupied_q |-> !opc_read_req_valid_o[i])
                else $error("Operand %0d requested while not occupied", i);

            // Assert that we do not receive an operand if we are not occupied or have not requested it or are already ready
            assert property (@(posedge clk_i) !occupied_q || !operand_requested_q[i]
                                            || operand_ready_q[i] |-> !opc_read_rsp_valid_i[i])
                else $error("Operand %0d received while not occupied or not requested or ready", i);
        end : gen_operand_assertions
    `endif

endmodule : operand_collector
