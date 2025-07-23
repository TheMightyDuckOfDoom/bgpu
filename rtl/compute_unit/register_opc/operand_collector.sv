// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "common_cells/registers.svh"

/// Operand Collector
module operand_collector import bgpu_pkg::*; #(
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
    input  inst_t     disp_inst_i,
    input  reg_idx_t  disp_dst_i,
    input  logic      [OperandsPerInst-1:0] disp_src_required_i,
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
    output inst_t      opc_inst_o,
    output reg_idx_t   opc_dst_o,
    output warp_data_t [OperandsPerInst-1:0] opc_operand_data_o
);

    // #######################################################################################
    // # Type Definitions                                                                    #
    // #######################################################################################

    typedef struct packed {
        logic       occupied; // Is the collector occupied with an instruction?
        iid_t       tag;      // Instruction Tag
        pc_t        pc;       // Instruction Program Counter
        act_mask_t  act_mask; // Instruction Activate Mask
        inst_t      inst;     // Instruction
        reg_idx_t   dst;      // Instruction Destination Register Index
    } common_t;

    typedef struct packed {
        logic       requested;
        logic       ready;
        reg_idx_t   reg_idx;
        warp_data_t data;
    } operand_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Common Data
    common_t common_q, common_d;

    // Per Operand Data
    operand_t [OperandsPerInst-1:0] operand_q, operand_d;

    // Combined Operand Ready and Data
    logic                             operands_ready;

    // ########################################################################################
    // # Sequential Logic                                                                    #
    // ########################################################################################

    // Operand Request Logic
    for (genvar i = 0; i < OperandsPerInst; i++) begin : gen_operand_request
        always_comb begin : operand_request_logic
            // Default Register Data
            operand_d[i] = operand_q[i];

            // Operand Data
            opc_operand_data_o[i] = operand_q[i].data;

            // Default Outputs |-> make request
            opc_read_req_valid_o  [i] = !operand_q[i].requested && common_q.occupied;
            opc_read_req_reg_idx_o[i] =  operand_q[i].reg_idx;
            opc_read_req_wid_o    [i] = common_q.tag[WidWidth-1:0];

            // Request handshake
            if (opc_read_req_valid_o[i] && opc_read_req_ready_i[i]) begin : request_handshake
                // We have requested the operand
                operand_d[i].requested = 1'b1;
            end : request_handshake

            // Receiveing the operand data
            if (opc_read_rsp_valid_i[i]) begin : receive_operand_data
                // We have received the operand data
                operand_d[i].ready = 1'b1;
                operand_d[i].data  = opc_read_rsp_data_i[i];
            end : receive_operand_data

            // Insert new instruction |-> Handshake
            if (disp_valid_i && opc_ready_o) begin : new_instruction
                // If we do not require the operand, we are ready and have already requested it
                operand_d[i].requested = !disp_src_required_i[i];
                operand_d[i].ready     = !disp_src_required_i[i];
                if (disp_src_required_i[i])
                    operand_d[i].reg_idx = disp_src_i[i];
                else begin : operands_not_required
                    // Store register index of operands in the data
                    operand_d[i].data = '0;
                    for (int thread = 0; thread < WarpWidth; thread++) begin
                        // Load {operand1, operand2} register index into data
                        operand_d[i].data[thread * RegWidth + i * RegIdxWidth +: RegIdxWidth]
                            = disp_src_i[i];
                    end
                end : operands_not_required
            end : new_instruction
        end : operand_request_logic
    end : gen_operand_request

    // Instruction Logic
    always_comb begin : instruction_logic
        // Default Register Data
        common_d = common_q;

        // Insert new instruction |-> Handshake
        if (disp_valid_i && opc_ready_o) begin : new_instruction
            common_d.occupied = 1'b1; // We are now occupied
            common_d.tag      = disp_tag_i;
            common_d.pc       = disp_pc_i;
            common_d.act_mask = disp_act_mask_i;
            common_d.inst     = disp_inst_i;
            common_d.dst      = disp_dst_i;
        end : new_instruction

        // Output Handshake
        if (eu_ready_i && opc_valid_o) begin : output_handshake
            common_d.occupied = 1'b0; // We are no longer occupied
        end : output_handshake
    end : instruction_logic

    // Are the operands ready?
    always_comb begin : operand_ready_logic
        operands_ready = 1'b1;
        for (int i = 0; i < OperandsPerInst; i++) begin : check_operand_ready
            // If the operand is not ready, we are not ready
            if (!operand_q[i].ready) begin
                operands_ready = 1'b0;
            end
        end : check_operand_ready
    end : operand_ready_logic

    // We are ready to accept a new instruction if we are not occupied
    assign opc_ready_o = !common_q.occupied;

    // Outputs to Execution Units
    assign opc_valid_o        = common_q.occupied && operands_ready;
    assign opc_tag_o          = common_q.tag;
    assign opc_pc_o           = common_q.pc;
    assign opc_act_mask_o     = common_q.act_mask;
    assign opc_inst_o         = common_q.inst;
    assign opc_dst_o          = common_q.dst;

    // ########################################################################################
    // # Sequential Logic                                                                     #
    // ########################################################################################

    // Common
    `FF(common_q, common_d, '0, clk_i, rst_ni);

    // Operands
    for (genvar i = 0; i < OperandsPerInst; i++) begin : gen_operand_ff
        `FF(operand_q[i], operand_d[i], '0, clk_i, rst_ni);
    end : gen_operand_ff

    // ########################################################################################
    // # Assertions                                                                           #
    // ########################################################################################

    // Operands
    `ifndef SYNTHESIS
        for (genvar i = 0; i < OperandsPerInst; i++) begin : gen_operand_assertions
            // Assert that we do not request an operand if we are not occupied
            assert property (@(posedge clk_i) !common_q.occupied |-> !opc_read_req_valid_o[i])
                else $error("Operand %0d requested while not occupied", i);

            // Assert that we do not receive an operand if we are not occupied or have not requested it or are already ready
            assert property (@(posedge clk_i) !common_q.occupied || !operand_q[i].requested
                                            || operand_q[i].ready |-> !opc_read_rsp_valid_i[i])
                else $error("Operand %0d received while not occupied or not requested or ready", i);
        end : gen_operand_assertions

        initial assert (OperandsPerInst * RegIdxWidth <= RegWidth)
            else $error("OperandsPerInst * RegIdxWidth (%0d) must be <= RegWidth (%0d)",
                        OperandsPerInst * RegIdxWidth, RegWidth);
    `endif

endmodule : operand_collector
