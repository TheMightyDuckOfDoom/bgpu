// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "common_cells/registers.svh"

/// Idependent Threads Scheduling Unit for a single warp
// Holds a seperate PC for each thread in the warp
// If a warp is divergent, then each thread can have a different PC
// Each time a thread diverges, a new PC is allocated
module warp_its_unit #(
    /// Width of the Program Counter
    parameter int unsigned PcWidth = 32,
    /// Number of threads per warp
    parameter int unsigned WarpWidth = 32,

    /// Dependent parameter, do **not** overwrite.
    parameter int unsigned SubwarpIdWidth = WarpWidth > 1 ? $clog2(WarpWidth) : 1,
    parameter type pc_t         = logic [       PcWidth-1:0],
    parameter type act_mask_t   = logic [     WarpWidth-1:0],
    parameter type subwarp_id_t = logic [SubwarpIdWidth-1:0]
) (
    /// Clock and reset
    input logic clk_i,
    input logic rst_ni,

    // Initialization
    input logic init_i,
    input pc_t  init_pc_i,

    // To / From Fetcher
    input  logic        selected_for_fetch_i,
    output logic        ready_for_fetch_o,
    output pc_t         fetch_pc_o,
    output act_mask_t   fetch_act_mask_o,
    output subwarp_id_t fetch_subwarp_id_o,

    output logic        all_threads_finished_o, // All threads have reached a stop instruction

    // From Decoder
    input logic        instruction_decoded_i,
    input logic        stop_warp_i,
    input logic        is_branch_i,
    input subwarp_id_t decoded_subwarp_id_i,
    input pc_t         next_pc_i,

    // From Branch Unit
    input logic      bru_branch_i,         // New branch instruction
    input act_mask_t bru_branching_mask_i, // Active threads for the branch
    input pc_t       bru_branch_pc_i       // PC to branch to for the threads in the mask
);
    // #######################################################################################
    // # Local Parameters                                                                    #
    // #######################################################################################

    // #######################################################################################
    // # Typedefs                                                                            #
    // #######################################################################################

    typedef struct packed {
        pc_t       pc;
        act_mask_t active_mask;
    } pc_act_mask_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Program Counter is in use
    logic [WarpWidth-1:0] valid_pc_q, valid_pc_d;

    // Program Counter and active mask for each thread
    pc_act_mask_t [WarpWidth-1:0] pc_act_mask_q, pc_act_mask_d;

    // Is the PC ready for fetching?
    logic [WarpWidth-1:0] pc_ready_d, pc_ready_q;

    // Are the threads waiting for a sync?
    logic [WarpWidth-1:0] sync_waiting_d, sync_waiting_q;

    // PCs that are ready for fetching
    logic [WarpWidth-1:0] ready_for_fetch;

    // PC selected for fetching
    logic [WarpWidth-1:0] pc_selected_for_fetch;
    pc_act_mask_t         selected_pc_act_mask;

    // Uniform branch
    logic is_branch_uniform;

    // #######################################################################################
    // # Combinatorial Logic                                                                 #
    // #######################################################################################

    // Main logic
    always_comb begin : main_logic
        // Default
        valid_pc_d     = valid_pc_q;
        pc_act_mask_d  = pc_act_mask_q;
        pc_ready_d     = pc_ready_q;
        sync_waiting_d = sync_waiting_q;

        is_branch_uniform = 1'b0;

        // Initialization
        if (init_i) begin : init_pcs
            // Reset all PCs and masks
            valid_pc_d     = '0; // Invalidate all PCs
            pc_act_mask_d  = '0; // Reset all PCs and active masks
            pc_ready_d     = '0; // Reset all PC ready flags to zero
            sync_waiting_d = '0; // Reset all sync waiting flags to zero

            // Single PC for all threads
            valid_pc_d   [0]             = 1'b1;
            pc_act_mask_d[0].pc          = init_pc_i;
            pc_act_mask_d[0].active_mask = '1;
            pc_ready_d   [0]             = 1'b1;
        end : init_pcs
        else begin : normal_operation
            for (int unsigned i = 0; i < WarpWidth; i++) begin : loop_pcs
                if (valid_pc_q[i]) begin : valid_pc
                    // PC is selected for fetching
                    if (pc_selected_for_fetch[i]) begin : selected_for_fetch
                        // No longer ready for fetching
                        pc_ready_d[i] = 1'b0;
                    end : selected_for_fetch

                    // Decoded instruction by the Decoder
                    if (instruction_decoded_i
                        && (decoded_subwarp_id_i == i[SubwarpIdWidth-1:0]))
                    begin : decoded_normal_instruction
                        // Update PC to next instruction
                        pc_act_mask_d[i].pc = next_pc_i;
                        // We are ready again for fetching if it was not a branch instruction
                        pc_ready_d[i] = (!is_branch_i);

                        // If it is a stop instruction, then we can deallocate the PC
                        if (stop_warp_i) begin : stop_subwarp
                            pc_ready_d[i] = 1'b0;
                            valid_pc_d[i] = 1'b0;
                        end : stop_subwarp
                    end : decoded_normal_instruction

                    // Branch from Branch Unit
                    if (bru_branch_i) begin
                        // Check if all active threads are branching
                        if (pc_act_mask_q[i].active_mask == bru_branching_mask_i)
                        begin : branch_all_active
                            // All threads are branching to the same target PC
                            pc_act_mask_d[i].pc = bru_branch_pc_i;

                            // Set uniform branch flag
                            is_branch_uniform = 1'b1;
                        end : branch_all_active
                        // Check if some threads are branching
                        else if (bru_branching_mask_i != '0) begin : branch_some_active
                            // Mask off the branching threads from using this PC
                            pc_act_mask_d[i].active_mask = pc_act_mask_q[i].active_mask
                                                            & (~bru_branching_mask_i);
                        end : branch_some_active

                        // We are ready again for fetching
                        pc_ready_d[i] = 1'b1;
                    end
                end : valid_pc
            end : loop_pcs

            // If a branch is not uniform, then we need to allocate a new PC
            if (bru_branch_i && (!is_branch_uniform)) begin : allocate_new_pc
                // Find first free PC
                for (int unsigned i = 0; i < WarpWidth; i++) begin : loop_over_free_pcs
                    if (!valid_pc_q[i]) begin : found_free_pc
                        // Allocate new PC
                        valid_pc_d[i]                = 1'b1;
                        pc_act_mask_d[i].pc          = bru_branch_pc_i;
                        pc_act_mask_d[i].active_mask = bru_branching_mask_i;

                        // Is ready for fetching
                        pc_ready_d[i]                = 1'b1;

                        // No need to check further, we found a free PC
                        break;
                    end : found_free_pc
                end : loop_over_free_pcs
            end : allocate_new_pc
        end : normal_operation
    end : main_logic

    // PCs are ready for fetching if they are ready and not waiting for a sync
    assign ready_for_fetch = valid_pc_q & pc_ready_q & (~sync_waiting_q);

    // Arbitration logic among ready PCs
    rr_arb_tree #(
        .NumIn    ( WarpWidth     ),
        .DataType ( pc_act_mask_t ),
        .ExtPrio  ( 1'b0          ),
        .AxiVldRdy( 1'b0          ),
        .LockIn   ( 1'b0          ),
        .FairArb  ( 1'b1          )
    ) i_rr_arb (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .req_i ( ready_for_fetch       ),
        .gnt_o ( pc_selected_for_fetch ),
        .data_i( pc_act_mask_q         ),

        .req_o ( ready_for_fetch_o    ),
        .gnt_i ( selected_for_fetch_i ),
        .data_o( selected_pc_act_mask ),
        .idx_o ( fetch_subwarp_id_o   ),

        .flush_i( 1'b0         ),
        .rr_i   ( '0           )
    );

    assign fetch_pc_o       = selected_pc_act_mask.pc;
    assign fetch_act_mask_o = selected_pc_act_mask.active_mask;

    // All threads have reached a stop if no PC is valid anymore
    assign all_threads_finished_o = valid_pc_q == '0;

    // #######################################################################################
    // # Sequential Logic                                                                    #
    // #######################################################################################

    `FF(valid_pc_q,     valid_pc_d,     '0, clk_i, rst_ni)
    `FF(pc_act_mask_q,  pc_act_mask_d,  '0, clk_i, rst_ni)
    `FF(pc_ready_q,     pc_ready_d,     '0, clk_i, rst_ni)
    `FF(sync_waiting_q, sync_waiting_d, '0, clk_i, rst_ni)

    // #######################################################################################
    // # Assertions                                                                          #
    // #######################################################################################
    `ifndef SYNTHESIS
        // We can never be selected for fetching if we are not ready
        assert property (@(posedge clk_i) disable iff (!rst_ni) selected_for_fetch_i
                                                                    |-> ready_for_fetch != '0)
            else $error("ITS: Selected for fetching but not ready!");

        // We can never be decoded if we are ready
        assert property (@(posedge clk_i) disable iff (!rst_ni) instruction_decoded_i
                                                     |-> !ready_for_fetch[decoded_subwarp_id_i])
            else $error("ITS: Instruction decoded but ready for fetching!");

        // Decoded instruction must be for a valid subwarp
        assert property (@(posedge clk_i) disable iff (!rst_ni) instruction_decoded_i
                                        |-> valid_pc_q[decoded_subwarp_id_i])
            else $error("ITS: Instruction decoded but no valid PC for subwarp %0d!",
                        decoded_subwarp_id_i);

        for(genvar i = 0; i < WarpWidth; i++) begin : gen_assertions
            // If a PC is valid, then it must have a active mask with at least one active thread
            assert property (@(posedge clk_i) disable iff (!rst_ni) valid_pc_q[i]
                |-> pc_act_mask_q[i].active_mask != '0)
                else $error("ITS: Valid PC but no active threads in active mask!");
        end : gen_assertions
    `endif
endmodule : warp_its_unit
