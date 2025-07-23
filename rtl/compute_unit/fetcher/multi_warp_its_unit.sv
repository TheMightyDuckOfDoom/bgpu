// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "common_cells/registers.svh"

/// General Information Storage and ITS units for multiple warps
module multi_warp_its_unit #(
    /// Width of the Program Counter
    parameter int unsigned PcWidth = 32,
    /// Number of warps per compute unit
    parameter int unsigned NumWarps = 32,
    /// Number of threads per warp
    parameter int unsigned WarpWidth = 32,
    // How many bits are used to index thread blocks inside a thread group?
    parameter int unsigned TblockIdxBits = 4,
    // How many bits are used to identify a thread block?
    parameter int unsigned TblockIdBits = 4,
    // Memory Address width in bits
    parameter int unsigned AddressWidth = 32,

    /// Dependent parameter, do **not** overwrite.
    parameter int unsigned WidWidth        = NumWarps > 1 ? $clog2(NumWarps)  : 1,
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

    /// From decode stage |-> is the instruction a branch or update normally to next instruction?
    input logic        instruction_decoded_i,
    input logic        decode_stop_warp_i,
    input wid_t        decode_wid_i,
    input subwarp_id_t decode_subwarp_id_i,
    input logic        decode_branch_i,
    input pc_t         decode_next_pc_i,

    /// From instruction buffer
    // Are there any instructions in flight?
    input  logic [NumWarps-1:0] ib_all_instr_finished_i,

    /// To/From Fetcher
    input  logic        [NumWarps-1:0] warp_selected_i,
    output logic        [NumWarps-1:0] warp_ready_o,
    output pc_t         [NumWarps-1:0] warp_pc_o,
    output act_mask_t   [NumWarps-1:0] warp_act_mask_o,
    output subwarp_id_t [NumWarps-1:0] warp_subwarp_id_o,

    /// To Integer Unit
    output addr_t       [NumWarps-1:0] warp_dp_addr_o,    // Data / Parameter address
    output tblock_idx_t [NumWarps-1:0] warp_tblock_idx_o, // Block index,

    // From Branch Unit
    input logic      bru_branch_i,      // New branch instruction
    input wid_t      bru_branch_wid_i,  // Which warp is the branch for?
    input act_mask_t bru_branching_mask_i, // Active threads for the branch
    input pc_t       bru_inactive_pc_i  // PC to execute for inactive threads
);
    // #######################################################################################
    // # Typedefs                                                                            #
    // #######################################################################################

    // Data per warp
    typedef struct packed {
        logic        occupied;
        logic        finished;
        addr_t       dp_addr;    // Data / Parameter address
        tblock_idx_t tblock_idx; // Block index -> used to calculate the thread id
        tblock_id_t  tblock_id;  // Unique identifier for the block
    } warp_data_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // General stack data
    warp_data_t [NumWarps-1:0] warp_data_q, warp_data_d;

    logic [NumWarps-1:0] allocate_warp;
    logic [NumWarps-1:0] warp_ready;

    // #######################################################################################
    // # Combinatorial Logic                                                                 #
    // #######################################################################################

    // Next PC and ready logic
    always_comb begin : next_pc_ready_logic
        // Default
        warp_data_d[NumWarps-1:0] = warp_data_q[NumWarps-1:0];

        tblock_done_o = 1'b0;
        tblock_done_id_o = '0;

        allocate_warp = '0;

        // Allocate a new warp
        if (allocate_warp_i && warp_free_o) begin : allocate_new_warp
            // Find the first free warp
            for (int i = 0; i < NumWarps; i++) begin : find_free_warp
                if (!warp_data_q[i].occupied) begin
                    // Allocate the warp
                    allocate_warp[i] = 1'b1;

                    // Set the initial values
                    warp_data_d[i].occupied   = 1'b1;
                    warp_data_d[i].finished   = 1'b0;
                    warp_data_d[i].tblock_idx = allocate_tblock_idx_i;
                    warp_data_d[i].tblock_id  = allocate_tblock_id_i;
                    warp_data_d[i].dp_addr    = allocate_dp_addr_i;
                    break;
                end
            end : find_free_warp
        end : allocate_new_warp

        // Did we get an update from decode?
        if (instruction_decoded_i) begin : decode_update
            // If the warp is finished |-> mark it as finished,
            // wait until all instructions are finished
            if (decode_stop_warp_i) begin
                warp_data_d[decode_wid_i].finished = 1'b1;
            end
        end : decode_update

        for (int i = 0; i < NumWarps; i++) begin : update
            // If the warp is finished and all instructions are finished |-> deallocate the warp and notify
            if (warp_data_q[i].occupied && warp_data_q[i].finished
                && ib_all_instr_finished_i[i] && (!tblock_done_o)) begin

                tblock_done_o    = 1'b1;
                tblock_done_id_o = warp_data_q[i].tblock_id;

                // Deallocate the warp upon handshake
                if (tblock_done_ready_i) begin
                    warp_data_d[i].occupied = 1'b0;
                    warp_data_d[i].finished = 1'b0;
                end
            end
        end : update
    end : next_pc_ready_logic

    // We can allocate a new warp if there is at least one warp that is not active
    always begin : warp_free
        warp_free_o = 1'b0;
        for (int i = 0; i < NumWarps; i++) begin : check
            if (!warp_data_q[i].occupied) begin
                warp_free_o = 1'b1;
            end
        end
    end : warp_free

    // #######################################################################################
    // # Sequential Logic                                                                    #
    // #######################################################################################

    `FF(warp_data_q, warp_data_d, '0, clk_i, rst_ni)

    // #######################################################################################
    // # Per Warp ITS units                                                                  #
    // #######################################################################################

    for (genvar warp = 0; warp < NumWarps; warp++) begin : gen_its_unit
        warp_its_unit #(
            .PcWidth  ( PcWidth   ),
            .WarpWidth( WarpWidth )
        ) i_warp_its (
            .clk_i ( clk_i  ),
            .rst_ni( rst_ni ),

            .init_i   ( allocate_warp[warp] ),
            .init_pc_i( allocate_pc_i       ),

            // From decode stage
            .instruction_decoded_i( instruction_decoded_i && (decode_wid_i == warp) ),
            .decoded_subwarp_id_i ( decode_subwarp_id_i                             ),
            .is_branch_i          ( decode_branch_i                                 ),
            .next_pc_i            ( decode_next_pc_i                                ),

            // From fetcher
            .selected_for_fetch_i( warp_selected_i[warp] ),

            // Stack outputs
            .ready_for_fetch_o ( warp_ready       [warp] ),
            .fetch_pc_o        ( warp_pc_o        [warp] ),
            .fetch_act_mask_o  ( warp_act_mask_o  [warp] ),
            .fetch_subwarp_id_o( warp_subwarp_id_o[warp] )

            // From branch unit
            // .bru_branch_i        ( bru_branch_i && (bru_branch_wid_i == warp) ),
            // .bru_branching_mask_i( bru_branching_mask_i                       ),
            // .bru_inactive_pc_i   ( bru_inactive_pc_i                          )
        );
    end : gen_its_unit

    // #######################################################################################
    // # Outputs                                                                             #
    // #######################################################################################

    for (genvar i = 0; i < NumWarps; i++) begin : gen_assign_outputs
        assign warp_ready_o     [i] = warp_ready[i] && warp_data_q[i].occupied
            && (|warp_act_mask_o[i]) && !warp_data_q[i].finished;
        assign warp_dp_addr_o   [i] = warp_data_q[i].dp_addr;
        assign warp_tblock_idx_o[i] = warp_data_q[i].tblock_idx;
    end : gen_assign_outputs

    // #######################################################################################
    // # Asserts                                                                             #
    // #######################################################################################

    `ifndef SYNTHESIS
        for (genvar i = 0; i < NumWarps; i++) begin : gen_asserts
            // Check that a ready warp has at least one active thread |-> otherwise we waste resources
            assert property (@(posedge clk_i) disable iff (!rst_ni)
                (!warp_ready_o[i] || (warp_ready_o[i] && warp_act_mask_o[i] != '0)))
            else $error("Warp is marked as ready, but no thread is active");

            assert property (@(posedge clk_i) disable iff (!rst_ni)
                (warp_selected_i[i] |-> warp_data_q[i].occupied))
            else $error("Warp was selected for fetching, but is not occupied: %0d", i);

            assert property (@(posedge clk_i) disable iff (!rst_ni)
                (warp_selected_i[i] |-> (|warp_act_mask_o[i])))
            else $error("Warp was selected for fetching, but is no thread is active: %0d", i);

            assert property (@(posedge clk_i) disable iff (!rst_ni)
                (warp_selected_i[i] |-> |warp_act_mask_o[i]))
            else $error("Warp was selected for fetching, but active mask is zero: %0d", i);

        end : gen_asserts

        // A warp cannot be selected and be decoded at the same time
        assert property (@(posedge clk_i) disable iff (!rst_ni)
            (instruction_decoded_i |-> !warp_selected_i[decode_wid_i]))
        else $error("Warp was selected for fetching, but got decoded at the same time: %0d",
            decode_wid_i);

        // Check that a warp that was decoded is occupied
        assert property (@(posedge clk_i) disable iff (!rst_ni)
            instruction_decoded_i |-> warp_data_q[decode_wid_i].occupied)
        else $error("Warp was decoded, but is not occupied: %0d", decode_wid_i);

    `endif

endmodule : multi_warp_its_unit
