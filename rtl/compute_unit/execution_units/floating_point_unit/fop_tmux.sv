// Copyright 2026 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "common_cells/registers.svh"

/// Time-Multiplexed Floating Point Operation
module fop_tmux #(
    // Number of threads in a warp
    parameter int unsigned WarpWidth = 4,
    /// Number of FOp-Units present
    // How many fop units are actually implemented
    parameter int unsigned NumFopUnits = 1,
    /// Width of the Operands
    parameter int DataWidth = 32,
    /// Operation to be implemented by this unit
    parameter string Operation = "DIV",
    /// Latency of the unit
    parameter int unsigned Latency = 8,
    /// Tag to be passed down the pipeline
    parameter type tag_t = logic,
    /// Dependent parameter, do **not** overwrite.
    parameter type data_t = logic [DataWidth-1:0]
) (
    // Clock and Reset
    input logic clk_i,
    input logic rst_ni,

    // Operands
    input  tag_t  tag_i,
    output logic  ready_o,
    input  logic  [WarpWidth-1:0] valid_i,
    input  data_t [WarpWidth-1:0] operand_a_i,
    input  data_t [WarpWidth-1:0] operand_b_i,

    // Result
    output logic  [WarpWidth-1:0] valid_o,
    output tag_t  [WarpWidth-1:0] tag_o,
    output data_t [WarpWidth-1:0] result_o
);
    // #######################################################################################
    // # Local parameters                                                                    #
    // #######################################################################################

    // Time-Multiplexing factor per Unit, each unit must do this many operations
    parameter int WidthPerUnit = WarpWidth / NumFopUnits;

    // Width index
    parameter int unsigned IdxWidth = WidthPerUnit > 1 ? $clog2(WidthPerUnit) : 1; 

    // Thread index width
    parameter int unsigned ThreadIdxWidth = WarpWidth > 1 ? $clog2(WarpWidth) : 1;

    // #######################################################################################
    // # Type Definitions                                                                    #
    // #######################################################################################

    // Index
    // Tracks which operation a unit is currently executing
    typedef logic [IdxWidth-1:0] idx_t;

    // Fop tag
    typedef struct packed {
        tag_t tag;
        idx_t idx;
    } fop_tag_t;

    // Fop request
    typedef struct packed {
        logic     valid;
        fop_tag_t fop_tag;
        data_t    operand_a;
        data_t    operand_b;
    } fop_req_t;

    // Fop result
    typedef struct packed {
        logic     valid;
        fop_tag_t fop_tag;
        data_t    result;
    } fop_res_t;

    // Pending operations
    typedef logic [WarpWidth-1:0] pend_op_t;

    // Thread index
    typedef logic [ThreadIdxWidth-1:0] tidx_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Pending operations
    pend_op_t pend_op_q, pend_op_d;
    // Tag of the pending operations
    tag_t op_tag_q, op_tag_d;
    // Operands
    data_t [WarpWidth-1:0] operand_a_q, operand_a_d;
    data_t [WarpWidth-1:0] operand_b_q, operand_b_d;
    // Idx counter
    idx_t idx_q, idx_d;

    // Fop Units
    fop_req_t [NumFopUnits-1:0] fop_req;
    fop_res_t [NumFopUnits-1:0] fop_res;

    // #######################################################################################
    // # Combinational Logic                                                                 #
    // #######################################################################################

    // Next State
    always_comb begin : next_state_logic
        // Default
        pend_op_d   = pend_op_q;
        op_tag_d    = op_tag_q;
        operand_a_d = operand_a_q;
        operand_b_d = operand_b_q;
        idx_d       = idx_q;

        fop_req = '0;
        ready_o = 1'b0;

        if (pend_op_q != '0) begin : issue_operation
            // Issue operation to units
            for (int i = 0; i < NumFopUnits; i++) begin
                fop_req[i].valid       = pend_op_q[tidx_t'(i * WidthPerUnit) + tidx_t'(idx_q)];
                fop_req[i].fop_tag.tag = op_tag_q;
                fop_req[i].fop_tag.idx = idx_q;
                fop_req[i].operand_a   = operand_a_q[tidx_t'(i * WidthPerUnit) + tidx_t'(idx_q)];
                fop_req[i].operand_b   = operand_b_q[tidx_t'(i * WidthPerUnit) + tidx_t'(idx_q)];

                // Mark as done
                pend_op_d[tidx_t'(i * WidthPerUnit) + tidx_t'(idx_q)] = 1'b0;
            end

            // Increment idx
            idx_d = idx_q + 'd1;
        end : issue_operation

        // Ready if all operations have been issued
        ready_o = pend_op_d == '0;

        // New Operation
        if (ready_o && (valid_i != '0)) begin
            // Store new operation info
            pend_op_d   = valid_i;
            op_tag_d    = tag_i;
            operand_a_d = operand_a_i;
            operand_b_d = operand_b_i;
            
            // Reset idx
            idx_d = '0;
        end
    end : next_state_logic

    // Results
    always_comb begin : result_logic
        // Default
        valid_o  = '0;
        tag_o    = '0;
        result_o = '0;

        for (int i = 0; i < NumFopUnits; i++) begin : loop_fop_units
            if (fop_res[i].valid) begin : fop_result_valid
                valid_o [tidx_t'(i * WidthPerUnit) + tidx_t'(fop_res[i].fop_tag.idx)] = 1'b1;
                tag_o   [tidx_t'(i * WidthPerUnit) + tidx_t'(fop_res[i].fop_tag.idx)] = fop_res[i].fop_tag.tag;
                result_o[tidx_t'(i * WidthPerUnit) + tidx_t'(fop_res[i].fop_tag.idx)] = fop_res[i].result;
            end : fop_result_valid
        end : loop_fop_units
    end : result_logic

    // #######################################################################################
    // # Sequential Logic                                                                    #
    // #######################################################################################

    `FF(pend_op_q,     pend_op_d, '0, clk_i, rst_ni)
    `FF(op_tag_q,       op_tag_d, '0, clk_i, rst_ni)
    `FF(idx_q,             idx_d, '0, clk_i, rst_ni)
    `FF(operand_a_q, operand_a_d, '0, clk_i, rst_ni)
    `FF(operand_b_q, operand_b_d, '0, clk_i, rst_ni)

    // #######################################################################################
    // # Floating Point Operation                                                            #
    // #######################################################################################

    for (genvar i = 0; i < NumFopUnits; i++) begin : gen_fop_units
        fop #(
            .DataWidth( DataWidth ),
            .Operation( Operation ),
            .Latency  ( Latency   ),
            .tag_t    ( fop_tag_t )
        ) i_div (
            .clk_i ( clk_i  ),
            .rst_ni( rst_ni ),

            .valid_i    ( fop_req[i].valid     ),
            .tag_i      ( fop_req[i].fop_tag   ),
            .operand_a_i( fop_req[i].operand_a ),
            .operand_b_i( fop_req[i].operand_b ),

            .valid_o ( fop_res[i].valid   ),
            .tag_o   ( fop_res[i].fop_tag ),
            .result_o( fop_res[i].result  )
        );
    end : gen_fop_units

    // #######################################################################################
    // # Assertions                                                                          #
    // #######################################################################################

    initial assert(WarpWidth % NumFopUnits == 0)
        else $fatal(1, "NumFopUnits must divide WarpWidth evenly");

endmodule : fop_tmux
