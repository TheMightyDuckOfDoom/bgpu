// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Branch Unit
module branch_unit import bgpu_pkg::*; #(
    /// Number of inflight instructions per warp
    parameter int unsigned NumTags = 8,
    // Width of the registers
    parameter int unsigned RegWidth = 32,
    // Number of threads in a warp
    parameter int unsigned WarpWidth = 4,
    /// Number of warps per compute unit
    parameter int unsigned NumWarps = 8,
    // Number of operands per instruction
    parameter int unsigned OperandsPerInst = 2,
    /// How many registers can each warp access as operand or destination
    parameter int unsigned RegIdxWidth = 8,
    // Memory Address width in bits
    parameter int unsigned AddressWidth = 32,
    /// Width of the Program Counter
    parameter int unsigned PcWidth = 16,

    /// Dependent parameter, do **not** overwrite.
    parameter int unsigned TagWidth    = $clog2(NumTags),
    parameter int unsigned WidWidth = NumWarps > 1 ? $clog2(NumWarps) : 1,
    parameter type warp_data_t  = logic [RegWidth * WarpWidth-1:0],
    parameter type reg_idx_t    = logic [         RegIdxWidth-1:0],
    parameter type iid_t        = logic [   TagWidth+WidWidth-1:0],
    parameter type addr_t       = logic [        AddressWidth-1:0],
    parameter type pc_t         = logic [             PcWidth-1:0],
    parameter type act_mask_t   = logic [           WarpWidth-1:0],
    parameter type wid_t        = logic [            WidWidth-1:0]
) (
    // Clock and reset
    input logic clk_i,
    input logic rst_ni,

    // From Operand Collector
    output logic         eu_to_opc_ready_o,
    input  logic         opc_to_eu_valid_i,
    input  act_mask_t    opc_to_eu_act_mask_i,
    input  iid_t         opc_to_eu_tag_i,
    input  pc_t          opc_to_eu_pc_i,
    input  bru_subtype_e opc_to_eu_inst_sub_i,
    input  reg_idx_t     opc_to_eu_dst_i,
    input  warp_data_t   [OperandsPerInst-1:0] opc_to_eu_operands_i,

    // To Result Collector
    input  logic       rc_to_eu_ready_i,
    output logic       eu_to_rc_valid_o,
    output act_mask_t  eu_to_rc_act_mask_o,
    output iid_t       eu_to_rc_tag_o,
    output reg_idx_t   eu_to_rc_dst_o,
    output warp_data_t eu_to_rc_data_o,

    // To Fetcher
    output logic      bru_branch_o,      // New branch instruction
    output wid_t      bru_branch_wid_o,  // Branching warp ID
    output act_mask_t bru_branching_mask_o, // Active threads for the branch
    output pc_t       bru_inactive_pc_o  // PC to execute for inactive threads
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
        act_mask_t  act_mask;
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
            result[i] = '0; // Default value

            // Check instruction subtype and perform operation
            case (opc_to_eu_inst_sub_i)
                BRU_JMP: begin // Jump to address
                    result[i][PcWidth-1:0] = opc_to_eu_pc_i;
                end

                BRU_BNZ: begin // Branch if not zero
                    result[i] = operands[1][i] != '0 ? 'd1 : '0;
                end

                default: begin
                    result[i] = '1; // Default case, should not happen
                end
            endcase
        end : calc_result
    end : gen_result

    // Handle branch instruction
    always_comb begin : handle_branch
        // Default
        bru_branch_o         = 1'b0;
        bru_branching_mask_o = '0;
        bru_inactive_pc_o    = opc_to_eu_pc_i + 'd1;
        bru_branch_wid_o     = opc_to_eu_tag_i[WidWidth-1:0]; // Warp ID

        // Handshake
        if (eu_to_opc_ready_o && opc_to_eu_valid_i) begin
            if (opc_to_eu_inst_sub_i == BRU_BNZ) begin
                // New branch instruction
                bru_branch_o = 1'b1;

                for(int unsigned i = 0; i < WarpWidth; i++) begin
                    // Set active mask for threads that are not zero
                    bru_branching_mask_o[i] = opc_to_eu_act_mask_i[i] && (operands[1][i] != '0);
                end
            end
        end
    end : handle_branch

    // #######################################################################################
    // # Output Register                                                                     #
    // #######################################################################################

    // Build data to store in register
    assign eu_to_opc_d.tag      = opc_to_eu_tag_i;
    assign eu_to_opc_d.dst      = opc_to_eu_dst_i;
    assign eu_to_opc_d.data     = result;
    assign eu_to_opc_d.act_mask = opc_to_eu_act_mask_i;

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
    assign eu_to_rc_tag_o      = eu_to_opc_q.tag;
    assign eu_to_rc_dst_o      = eu_to_opc_q.dst;
    assign eu_to_rc_data_o     = eu_to_opc_q.data;
    assign eu_to_rc_act_mask_o = eu_to_opc_q.act_mask;

    // #######################################################################################
    // # Assertions                                                                          #
    // #######################################################################################

    `ifndef SYNTHESIS
        assert property (@(posedge clk_i) disable iff (!rst_ni)
            opc_to_eu_valid_i |-> opc_to_eu_inst_sub_i inside `BRU_VALID_SUBTYPES)
            else $error("Invalid instruction subtype: %0h", opc_to_eu_inst_sub_i);
    `endif

endmodule : branch_unit
