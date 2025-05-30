// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "bgpu/instructions.svh"

/// Integer Unit
// Performs integer alu operations
module integer_unit #(
    // Width of the regusters
    parameter int unsigned RegWidth = 32,
    // Number of threads in a warp
    parameter int unsigned WarpWidth = 4,
    // Number of operands per instruction
    parameter int unsigned OperandsPerInst = 2,
    // Tag data type
    parameter type iid_t     = logic,
    // Register index data type
    parameter type reg_idx_t = logic,

    /// Dependent parameter, do **not** overwrite.
    parameter type warp_data_t = logic [RegWidth * WarpWidth-1:0]
) (
    // Clock and reset
    input logic clk_i,
    input logic rst_ni,

    // From Operand Collector
    output logic               eu_to_opc_ready_o,
    input  logic               opc_to_eu_valid_i,
    input  iid_t               opc_to_eu_tag_i,
    input  bgpu_inst_subtype_e opc_to_eu_inst_sub_i,
    input  reg_idx_t           opc_to_eu_dst_i,
    input  warp_data_t         [OperandsPerInst-1:0] opc_to_eu_operands_i,

    // To Result Collector
    input  logic       rc_to_eu_ready_i,
    output logic       eu_to_rc_valid_o,
    output iid_t       eu_to_rc_tag_o,
    output reg_idx_t   eu_to_rc_dst_o,
    output warp_data_t eu_to_rc_data_o
);
    // #######################################################################################
    // # Type Definitions                                                                    #
    // #######################################################################################

    typedef logic      [ RegWidth-1:0] reg_data_t;
    typedef reg_data_t [WarpWidth-1:0] reg_data_per_thread_t;

    typedef struct packed {
        iid_t       tag;
        reg_idx_t   dst;
        warp_data_t data;
    } eu_to_opc_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    reg_data_per_thread_t [OperandsPerInst-1:0] operands;
    reg_data_per_thread_t result;

    eu_to_opc_t eu_to_opc_d, eu_to_opc_q;

    // #######################################################################################
    // # Combinational Logic                                                                 #
    // #######################################################################################

    // Extract operands
    for (genvar i = 0; i < OperandsPerInst; i++) begin : gen_extract_operands
        assign operands[i] = opc_to_eu_operands_i[i];
    end : gen_extract_operands

    // Calculate result
    for (genvar i = 0; i < WarpWidth; i++) begin : gen_result
        always_comb begin : calc_result
            case (opc_to_eu_inst_sub_i)
                IU_ADD:  result[i] = operands[0][i] + operands[1][i];
                IU_TID:  result[i] = i; // Thread ID
                IU_LDI:  result[i] = operands[0][i] | operands[1][i]; // Load immediate
                default: begin
                    result[i] = '0; // Default case, should not happen
                    `ifndef SYNTHESIS
                        $fatal("Instruction subtype not implemented: %0h", opc_to_eu_inst_sub_i);
                    `endif
                end
            endcase
        end : calc_result
    end : gen_result

    // #######################################################################################
    // # Output Register                                                                     #
    // #######################################################################################

    // Build data to store in register
    assign eu_to_opc_d.tag  = opc_to_eu_tag_i;
    assign eu_to_opc_d.dst  = opc_to_eu_dst_i;
    assign eu_to_opc_d.data = result;

    // Pipeline register
    stream_register #(
        .T( eu_to_opc_t )
    ) i_reg (
        .clk_i     ( clk_i  ),
        .rst_ni    ( rst_ni ),
        .clr_i     ( 1'b0   ),
        .testmode_i( 1'b0   ),

        .valid_i( opc_to_eu_valid_i ),
        .ready_o( eu_to_opc_ready_o ),
        .data_i ( eu_to_opc_d       ),

        .valid_o( eu_to_rc_valid_o ),
        .ready_i( rc_to_eu_ready_i ),
        .data_o ( eu_to_opc_q       )
    );

    // Assign outputs
    assign eu_to_rc_tag_o  = eu_to_opc_q.tag;
    assign eu_to_rc_dst_o  = eu_to_opc_q.dst;
    assign eu_to_rc_data_o = eu_to_opc_q.data;

    // #######################################################################################
    // # Assertions                                                                          #
    // #######################################################################################

    `ifndef SYNTHESIS
        assert property (@(posedge clk_i) disable iff (!rst_ni)
            opc_to_eu_valid_i |-> opc_to_eu_inst_sub_i inside `BGPU_INT_UNIT_VALID_SUBTYPES)
            else $error("Invalid instruction subtype: %0h", opc_to_eu_inst_sub_i);
    `endif

endmodule : integer_unit
