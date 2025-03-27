// Copyright March 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Dispatcher
// Contains a WaitBuffer, RegTable and a tag_queue
// When a new instruction is decoded:
// 1. Get a new tag from the tag_queue
// 2. Check Register Table if operands are still in flight i.e a tag is assigned to them othwise is ready
// 3. Mark the dst register as in flight -> being written by this instruction

// When all operands are ready:
// 1. Remove from wait buffer

// When instruction is done:
// 1. Check wait buffer if any instruction is waiting on this result -> tag matches, mark as ready
// 2. Update Register Table, clear tag for dst register
module dispatcher #(
    /// Number of inflight instructions
    parameter int NumTags = 8,
    /// Width of the Program Counter
    parameter int PcWidth = 32,
    /// Number of threads per warp
    parameter int WarpWidth = 32,
    /// How many instructions that wait on previous results can be buffered per warp
    parameter int WaitBufferSizePerWarp = 4,
    /// How many registers can each warp access as operand or destination
    parameter int RegIdxWidth = 6,
    /// How many operands each instruction can have
    parameter int OperandsPerInst = 2,

    parameter type dec_inst_t = logic,

    /// Dependent parameter, do **not** overwrite.
    parameter int TagWidth    = $clog2(NumTags),
    parameter type tag_t      = logic [   TagWidth-1:0],
    parameter type reg_idx_t  = logic [RegIdxWidth-1:0],
    parameter type pc_t       = logic [    PcWidth-1:0],
    parameter type act_mask_t = logic [  WarpWidth-1:0]
) (
    /// Clock and Reset
    input  logic clk_i,
    input  logic rst_ni,

    /// From fetcher -> which warp gets fetched next
    input  logic fe_handshake_i,

    /// To fetcher -> which warps have space for a new instruction?
    output logic ib_space_available_o,

    /// From decoder
    output logic      disp_ready_o,
    input  logic      dec_valid_i,
    input  pc_t       dec_pc_i,
    input  act_mask_t dec_act_mask_i,
    input  dec_inst_t dec_inst_i,

    /// To Operand Collector
    input  logic     opc_ready_i,
    output logic     disp_valid_o,
    output tag_t     disp_tag_o,
    output reg_idx_t disp_dst_o,
    output reg_idx_t [OperandsPerInst-1:0] disp_operands_o,

    /// From Execution Units
    input  logic eu_valid_i,
    input  tag_t eu_tag_i
);

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Insert handshake
    logic insert;

    // Tag Queue
    logic tag_available;
    tag_t dst_tag;
    logic tag_queue_ready;

    // Register Table
    logic reg_table_space_available;

    logic [OperandsPerInst-1:0] operands_ready;
    tag_t [OperandsPerInst-1:0] operands_tag;

    // Wait Buffer
    logic wb_ready;

    // #######################################################################################
    // # Combinational Logic                                                                 #
    // #######################################################################################

    // Disp ready if:
    // 1. Tag queue has a tag available
    // 2. Wait buffer has space
    // 3. Register table has space

    assign disp_ready_o = tag_available && wb_ready && reg_table_space_available;

    // Insert new element -> if handshake happens
    assign insert = dec_valid_i && disp_ready_o;

    // #######################################################################################
    // # Tag Queue                                                                           #
    // #######################################################################################

    tag_queue #(
        .NumTags(NumTags)
    ) i_tag_queue (
        .clk_i  ( clk_i  ),
        .rst_ni ( rst_ni ),

        .free_i( eu_valid_i ),
        .tag_i ( eu_tag_i   ),

        .get_i  ( insert        ),
        .tag_o  ( dst_tag       ),
        .valid_o( tag_available )
    );

    // #######################################################################################
    // # Register Table                                                                      #
    // #######################################################################################

    reg_table #(
        .NumTags(NumTags),
        .RegIdxWidth(RegIdxWidth),
        .OperandsPerInst(OperandsPerInst)
    ) i_reg_table (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .space_available_o( reg_table_space_available ),
        .insert_i         ( insert                    ),
        .tag_i            ( dst_tag                   ),
        .dst_reg_i        ( dec_inst_i.dst            ),
        .operands_reg_i   ( dec_inst_i.src            ),

        .operands_ready_o( operands_ready ),
        .operands_tag_o  ( operands_tag   ),

        .eu_valid_i( eu_valid_i ),
        .eu_tag_i  ( eu_tag_i   )
    );

    // #######################################################################################
    // # Wait Buffer                                                                         #
    // #######################################################################################

    wait_buffer #(
        .NumTags(NumTags),
        .PcWidth(PcWidth),
        .WarpWidth(WarpWidth),
        .WaitBufferSizePerWarp(WaitBufferSizePerWarp),
        .RegIdxWidth(RegIdxWidth),
        .OperandsPerInst(OperandsPerInst)
    ) i_wait_buffer (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .fe_handshake_i      ( fe_handshake_i       ),
        .ib_space_available_o( ib_space_available_o ),

        .wb_ready_o          ( wb_ready       ),
        .dec_valid_i         ( insert         ),
        .dec_pc_i            ( dec_pc_i       ),
        .dec_act_mask_i      ( dec_act_mask_i ),
        .dec_tag_i           ( dst_tag        ),
        .dec_dst_reg_i       ( dec_inst_i.dst ),
        .dec_operands_ready_i( operands_ready ),
        .dec_operand_tags_i  ( operands_tag   ),
        .dec_operands_i      ( dec_inst_i.src ),

        .opc_ready_i     ( opc_ready_i     ),
        .disp_valid_o    ( disp_valid_o    ),
        .disp_tag_o      ( disp_tag_o      ),
        .disp_dst_o      ( disp_dst_o      ),
        .disp_operands_o ( disp_operands_o ),

        .eu_valid_i( eu_valid_i ),
        .eu_tag_i  ( eu_tag_i   )
    );

    // #######################################################################################
    // # Assertions                                                                          #
    // #######################################################################################

    `ifndef SYNTHESIS
        initial assert(NumTags > WaitBufferSizePerWarp)
        else $error(1, "NumTags must be greater than WaitBufferSizePerWarp");

        assert property(@(posedge clk_i) disable iff(rst_ni) eu_valid_i |-> tag_queue_ready)
        else $error(1, "Tag queue must be ready to receive execution unit tags");
    `endif

endmodule : dispatcher
