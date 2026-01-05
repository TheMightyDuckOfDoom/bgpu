// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Dispatcher
// Contains a WaitBuffer, RegTable and a tag_queue
// When a new instruction is decoded:
// 1. Get a new tag from the tag_queue
// 2. Check Register Table if operands are still in flight i.e a tag is assigned to them othwise is ready
// 3. Mark the dst register as in flight |-> being written by this instruction

// When all operands are ready:
// 1. Remove from wait buffer

// When instruction is done:
// 1. Check wait buffer if any instruction is waiting on this result |-> tag matches, mark as ready
// 2. Update Register Table, clear tag for dst register
module dispatcher import bgpu_pkg::*; #(
    /// Number of instructions to fetch for the warp
    parameter int unsigned FetchWidth = 1,
    /// Number of instructions to dispatch simultaneously
    parameter int unsigned DispatchWidth = 1,
    /// Number of instructions that can write back simultaneously
    parameter int unsigned WritebackWidth = 1,
    /// Number of inflight instructions per warp
    parameter int unsigned NumTags = 8,
    /// Width of the Program Counter
    parameter int unsigned PcWidth = 32,
    /// Number of threads per warp
    parameter int unsigned WarpWidth = 32,
    /// How many registers can each warp access as operand or destination
    parameter int unsigned RegIdxWidth = 6,
    /// How many operands each instruction can have
    parameter int unsigned OperandsPerInst = 2,

    /// Dependent parameter, do **not** overwrite.
    parameter int unsigned TagWidth       = $clog2(NumTags),
    parameter int unsigned SubwarpIdWidth = WarpWidth > 1 ? $clog2(WarpWidth) : 1,
    parameter type         tag_t          = logic     [       TagWidth-1:0],
    parameter type         reg_idx_t      = logic     [    RegIdxWidth-1:0],
    parameter type         pc_t           = logic     [        PcWidth-1:0],
    parameter type         act_mask_t     = logic     [      WarpWidth-1:0],
    parameter type         subwarp_id_t   = logic     [ SubwarpIdWidth-1:0],
    parameter type         op_mask_t      = logic     [OperandsPerInst-1:0],
    parameter type         op_reg_idx_t   = reg_idx_t [OperandsPerInst-1:0]
) (
    /// Clock and Reset
    input  logic clk_i,
    input  logic rst_ni,

    /// Force instructions to execute in-order
    input  logic inorder_execution_i,

    /// From fetcher |-> which warp gets fetched next
    input  logic fe_handshake_i,

    /// To fetcher
    // which warps have space for a new instruction?
    output logic [FetchWidth-1:0] ib_space_available_o,
    // Have all destination registers been written to the register file?
    // -> All instructions finished
    output logic ib_all_instr_finished_o,

    /// From decoder -> Decoded instruction that does not need a wait buffer entry
    input logic [FetchWidth-1:0] dec_decoded_unused_ibe_i,

    /// From decoder -> new instruction
    output logic                         disp_ready_o,
    input  logic                         dec_valid_i,
    input  subwarp_id_t                  dec_subwarp_id_i,
    input  pc_t                          dec_pc_i,
    input  act_mask_t                    dec_act_mask_i,
    input  logic        [FetchWidth-1:0] dec_valid_insts_i,
    input  inst_t       [FetchWidth-1:0] dec_inst_i,
    input  reg_idx_t    [FetchWidth-1:0] dec_dst_i,
    input  op_mask_t    [FetchWidth-1:0] dec_operands_is_reg_i,
    input  op_reg_idx_t [FetchWidth-1:0] dec_operands_i,

    /// To Operand Collector
    input  logic        opc_ready_i,
    output logic        disp_valid_o,
    output tag_t        disp_tag_o,
    output pc_t         disp_pc_o,
    output act_mask_t   disp_act_mask_o,
    output inst_t       disp_inst_o,
    output reg_idx_t    disp_dst_o,
    output op_mask_t    disp_operands_is_reg_o,
    output op_reg_idx_t disp_operands_o,

    /// From Operand Collector -> instruction has read its operands
    input logic [DispatchWidth-1:0] opc_eu_handshake_i,
    input tag_t [DispatchWidth-1:0] opc_eu_tag_i,

    /// From Execution Units
    input  logic [WritebackWidth-1:0] eu_valid_i,
    input  tag_t [WritebackWidth-1:0] eu_tag_i
);
    // #######################################################################################
    // # Typedefs                                                                            #
    // #######################################################################################

    // Operand Tags
    typedef tag_t [OperandsPerInst-1:0] op_tag_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Insert handshake
    logic [FetchWidth-1:0] insert;

    // Tag Queue
    logic [FetchWidth-1:0] tag_available;
    tag_t [FetchWidth-1:0] dst_tag;
    logic tag_queue_ready;

    // Register Table
    logic reg_table_space_available;

    op_mask_t [FetchWidth-1:0] operands_ready;
    op_tag_t  [FetchWidth-1:0] operands_tag;

    // Wait Buffer
    logic wb_ready;

    // #######################################################################################
    // # Combinational Logic                                                                 #
    // #######################################################################################

    // Disp ready if we have tags available (implies space in reg table)
    // Wait buffer is ensured to be ready to accept new instructions by credit counter
    assign disp_ready_o = (tag_available & dec_valid_insts_i) == dec_valid_insts_i;

    // Insert new element |-> if handshake happens
    assign insert = dec_valid_i && disp_ready_o ? dec_valid_insts_i : '0;

    // #######################################################################################
    // # Tag Queue                                                                           #
    // #######################################################################################

    tag_queue #(
        .NumTagIn ( WritebackWidth ),
        .NumTagOut( FetchWidth     ),
        .NumTags  ( NumTags        )
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
        .FetchWidth     ( FetchWidth      ),
        .WritebackWidth ( WritebackWidth  ),
        .WarpWidth      ( WarpWidth       ),
        .NumTags        ( NumTags         ),
        .RegIdxWidth    ( RegIdxWidth     ),
        .OperandsPerInst( OperandsPerInst )
    ) i_reg_table (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .all_dst_written_o( ib_all_instr_finished_o ),

        .insert_i      ( insert           ),
        .subwarp_id_i  ( dec_subwarp_id_i ),
        .tag_i         ( dst_tag          ),
        .dst_reg_i     ( dec_dst_i        ),
        .operands_reg_i( dec_operands_i   ),

        .operands_ready_o( operands_ready ),
        .operands_tag_o  ( operands_tag   ),

        .eu_valid_i( eu_valid_i ),
        .eu_tag_i  ( eu_tag_i   )
    );

    // #######################################################################################
    // # Wait Buffer                                                                         #
    // #######################################################################################

    wait_buffer #(
        .FetchWidth     ( FetchWidth      ),
        .DispatchWidth  ( DispatchWidth   ),
        .WritebackWidth ( WritebackWidth  ),
        .NumTags        ( NumTags         ),
        .PcWidth        ( PcWidth         ),
        .WarpWidth      ( WarpWidth       ),
        .RegIdxWidth    ( RegIdxWidth     ),
        .OperandsPerInst( OperandsPerInst )
    ) i_wait_buffer (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .inorder_execution_i( inorder_execution_i ),

        .fe_handshake_i      ( fe_handshake_i       ),
        .ib_space_available_o( ib_space_available_o ),

        .dec_decoded_unused_ibe_i( dec_decoded_unused_ibe_i ),

        .dec_valid_i          ( insert                ),
        .dec_pc_i             ( dec_pc_i              ),
        .dec_act_mask_i       ( dec_act_mask_i        ),
        .dec_tag_i            ( dst_tag               ),
        .dec_inst_i           ( dec_inst_i            ),
        .dec_dst_reg_i        ( dec_dst_i             ),
        .dec_operands_is_reg_i( dec_operands_is_reg_i ),
        .dec_operands_ready_i ( operands_ready        ),
        .dec_operand_tags_i   ( operands_tag          ),
        .dec_operands_i       ( dec_operands_i        ),

        .opc_ready_i           ( opc_ready_i            ),
        .disp_valid_o          ( disp_valid_o           ),
        .disp_tag_o            ( disp_tag_o             ),
        .disp_pc_o             ( disp_pc_o              ),
        .disp_act_mask_o       ( disp_act_mask_o        ),
        .disp_inst_o           ( disp_inst_o            ),
        .disp_dst_o            ( disp_dst_o             ),
        .disp_operands_is_reg_o( disp_operands_is_reg_o ),
        .disp_operands_o       ( disp_operands_o        ),

        .opc_eu_handshake_i( opc_eu_handshake_i ),
        .opc_eu_tag_i      ( opc_eu_tag_i       ),

        .eu_valid_i( eu_valid_i ),
        .eu_tag_i  ( eu_tag_i   )
    );

endmodule : dispatcher
