// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Fetcher
/// contains the its unit
/// Outputs a PC to the instruction cache, if:
/// - There is space in the instruction buffer for a new instruction for a given warp
/// - The I-cache is ready to receive a new instruction to fetch
/// The PC of the warp comes from the its unit
/// If multiple warps are ready for fetching, a round-robin arbiter is used

module fetcher #(
    /// Width of the Program Counter
    parameter int unsigned PcWidth = 32,
    /// Number of warps per compute unit
    parameter int unsigned NumWarps = 8,
    /// Number of threads per warp
    parameter int unsigned WarpWidth = 32,
    // How many bits are used to index thread blocks inside a thread group?
    parameter int unsigned TblockIdxBits = 4,
    // How many bits are used to identify a thread block?
    parameter int unsigned TblockIdBits = 4,
    // Memory Address width in bits
    parameter int unsigned AddressWidth = 32,

    /// Dependent parameter, do **not** overwrite.
    parameter int unsigned WidWidth       =  NumWarps > 1 ? $clog2(NumWarps)  : 1,
    parameter int unsigned SubwarpIdWidth = WarpWidth > 1 ? $clog2(WarpWidth) : 1,
    parameter type tblock_idx_t = logic [ TblockIdxBits-1:0],
    parameter type tblock_id_t  = logic [  TblockIdBits-1:0],
    parameter type addr_t       = logic [  AddressWidth-1:0],
    parameter type wid_t        = logic [      WidWidth-1:0],
    parameter type pc_t         = logic [       PcWidth-1:0],
    parameter type act_mask_t   = logic [     WarpWidth-1:0],
    parameter type subwarp_id_t = logic [SubwarpIdWidth-1:0]
) (
    /// Clock and reset
    input logic clk_i,
    input logic rst_ni,

    // Interface to start a new thread block on this compute unit
    output logic        warp_free_o, // The is atleas one free warp that can start a new block
    input  logic        allocate_warp_i,
    input  pc_t         allocate_pc_i,
    input  addr_t       allocate_dp_addr_i, // Data / Parameter address
    input  tblock_idx_t allocate_tblock_idx_i, // Block index -> used to calculate the thread id
    input  tblock_id_t  allocate_tblock_id_i,  // Block id -> unique identifier for the block

    // Thread block completion
    input  logic       tblock_done_ready_i,
    output logic       tblock_done_o,
    output tblock_id_t tblock_done_id_o,

    /// From instruction buffer
    // Which warp has space for a new instruction?
    input  logic [NumWarps-1:0] ib_space_available_i,
    // Are there any instructions in flight?
    input  logic [NumWarps-1:0] ib_all_instr_finished_i,

    /// To/From instruction cache
    input  logic        ic_ready_i,
    output logic        fe_valid_o,
    output pc_t         fe_pc_o,
    output act_mask_t   fe_act_mask_o,
    output wid_t        fe_warp_id_o,
    output subwarp_id_t fe_subwarp_id_o,

    /// From Decoder
    input logic        dec_decoded_i,
    input logic        dec_stop_warp_i,
    input logic        dec_decoded_branch_i,
    input wid_t        dec_decoded_warp_id_i,
    input subwarp_id_t dec_decoded_subwarp_id_i,
    input pc_t         dec_decoded_next_pc_i,

    /// To Integer Unit
    output addr_t       [NumWarps-1:0] warp_dp_addr_o,    // Data / Parameter address
    output tblock_idx_t [NumWarps-1:0] warp_tblock_idx_o, // Block index

    // From Branch Unit
    input logic      bru_branch_i,      // New branch instruction
    input wid_t      bru_branch_wid_i,  // Which warp is the branch for?
    input act_mask_t bru_branching_mask_i, // Active threads for the branch
    input pc_t       bru_inactive_pc_i  // PC to execute for inactive threads
);
    // #######################################################################################
    // # Typedefs                                                                            #
    // #######################################################################################

    // Arbiter data input
    typedef struct packed {
        pc_t         pc;
        act_mask_t   act_mask;
        subwarp_id_t subwarp_id;
    } arb_warp_data_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Arbiter data input
    arb_warp_data_t [NumWarps-1:0] arb_in_data;
    logic [NumWarps-1:0] rr_warp_ready;

    // Arbiter data output
    arb_warp_data_t arb_sel_data;
    logic [NumWarps-1:0] arb_gnt;

    // Data from ITS unit
    logic        [NumWarps-1:0] its_warp_ready;
    pc_t         [NumWarps-1:0] its_warp_pc;
    act_mask_t   [NumWarps-1:0] its_warp_act_mask;
    subwarp_id_t [NumWarps-1:0] its_warp_subwarp_id;

    // #######################################################################################
    // # Round Robin Arbiter                                                                 #
    // #######################################################################################

    // Arbiter data input
    for(genvar i = 0; i < NumWarps; i++) begin : gen_arb_data
        assign arb_in_data[i].pc         = its_warp_pc        [i];
        assign arb_in_data[i].act_mask   = its_warp_act_mask  [i];
        assign arb_in_data[i].subwarp_id = its_warp_subwarp_id[i];
    end : gen_arb_data

    // Warp can be fetched if there is space in the instruction buffer and its unit is ready
    assign rr_warp_ready = ib_space_available_i & its_warp_ready;

    // Round robin arbiter
    rr_arb_tree #(
        .DataType ( arb_warp_data_t ),
        .NumIn    ( NumWarps ),
        .ExtPrio  ( 1'b0     ),
        .AxiVldRdy( 1'b0     ),
        .LockIn   ( 1'b1     ),
        .FairArb  ( 1'b1     )
    ) i_rr_arb (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .req_i  ( rr_warp_ready ),
        .gnt_o  ( arb_gnt       ),
        .data_i ( arb_in_data   ),

        // Directly to instruction cache
        .req_o ( fe_valid_o    ),
        .gnt_i ( ic_ready_i    ),
        .data_o( arb_sel_data  ),
        .idx_o ( fe_warp_id_o  ),

        // Unused
        .flush_i( 1'b0 ),
        .rr_i   ( '0   )
    );

    // #######################################################################################
    // # Independent Thread Scheduling Unit                                                  #
    // #######################################################################################

    multi_warp_its_unit #(
        .PcWidth      ( PcWidth       ),
        .NumWarps     ( NumWarps      ),
        .WarpWidth    ( WarpWidth     ),
        .AddressWidth ( AddressWidth  ),
        .TblockIdxBits( TblockIdxBits ),
        .TblockIdBits ( TblockIdBits  )
    ) i_its_unit (
        .clk_i             ( clk_i  ),
        .rst_ni            ( rst_ni ),

        .ib_all_instr_finished_i( ib_all_instr_finished_i ),

        .warp_free_o          ( warp_free_o           ),
        .allocate_warp_i      ( allocate_warp_i       ),
        .allocate_pc_i        ( allocate_pc_i         ),
        .allocate_dp_addr_i   ( allocate_dp_addr_i    ),
        .allocate_tblock_idx_i( allocate_tblock_idx_i ),
        .allocate_tblock_id_i ( allocate_tblock_id_i  ),

        .tblock_done_ready_i( tblock_done_ready_i ),
        .tblock_done_o      ( tblock_done_o       ),
        .tblock_done_id_o   ( tblock_done_id_o    ),

        .instruction_decoded_i( dec_decoded_i            ),
        .decode_stop_warp_i   ( dec_stop_warp_i          ),
        .decode_wid_i         ( dec_decoded_warp_id_i    ),
        .decode_subwarp_id_i  ( dec_decoded_subwarp_id_i ),
        .decode_branch_i      ( dec_decoded_branch_i     ),
        .decode_next_pc_i     ( dec_decoded_next_pc_i    ),

        .warp_selected_i  ( arb_gnt & rr_warp_ready ),
        .warp_ready_o     ( its_warp_ready          ),
        .warp_pc_o        ( its_warp_pc             ),
        .warp_act_mask_o  ( its_warp_act_mask       ),
        .warp_subwarp_id_o( its_warp_subwarp_id     ),

        .warp_dp_addr_o   ( warp_dp_addr_o    ),
        .warp_tblock_idx_o( warp_tblock_idx_o ),

        .bru_branch_i        ( bru_branch_i         ),
        .bru_branch_wid_i    ( bru_branch_wid_i     ),
        .bru_branching_mask_i( bru_branching_mask_i ),
        .bru_inactive_pc_i   ( bru_inactive_pc_i    )
    );

    // #######################################################################################
    // # Outputs                                                                             #
    // #######################################################################################

    // To instruction cache
    assign fe_pc_o         = arb_sel_data.pc;
    assign fe_act_mask_o   = arb_sel_data.act_mask;
    assign fe_subwarp_id_o = arb_sel_data.subwarp_id;

    // ########################################################################################
    // # Assertions                                                                           #
    // ########################################################################################

    `ifndef SYNTHESIS
        for (genvar i = 0; i < NumWarps; i++) begin : gen_asserts
            assert property (@(posedge clk_i) disable iff (!rst_ni)
                (its_warp_ready[i] |-> its_warp_act_mask[i] != '0))
            else $error("Warp is ready, but has no active threads");
        end : gen_asserts
    `endif

endmodule : fetcher
