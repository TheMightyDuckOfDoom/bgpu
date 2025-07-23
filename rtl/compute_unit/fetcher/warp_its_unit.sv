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

    // From Decoder
    input logic        instruction_decoded_i,
    input logic        is_branch_i,
    input subwarp_id_t decoded_subwarp_id_i,
    input pc_t         next_pc_i
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

    // #######################################################################################
    // # Combinatorial Logic                                                                 #
    // #######################################################################################

    // Main logic
    always_comb begin : main_logic
        // Default
        pc_act_mask_d  = pc_act_mask_q;
        pc_ready_d     = pc_ready_q;
        sync_waiting_d = sync_waiting_q;

        // Initialization
        if (init_i) begin : init_pcs
            // Reset all PCs and masks
            pc_act_mask_d  = '0; // Reset all PCs and active masks
            pc_ready_d     = '0; // Reset all PC ready flags to zero
            sync_waiting_d = '0; // Reset all sync waiting flags to zero

            // Single PC for all threads
            pc_act_mask_d[1].pc          = init_pc_i;
            pc_act_mask_d[1].active_mask = '1;
            pc_ready_d   [1]             = 1'b1;
        end : init_pcs
        else begin : normal_operation
            for (int unsigned i = 0; i < WarpWidth; i++) begin : loop_pcs
                // PC is selcted for fetching
                if (pc_selected_for_fetch[i]) begin : selected_for_fetch
                    // No longer ready for fetching
                    pc_ready_d[i] = 1'b0;
                end : selected_for_fetch
                // PC got decoded
                else if (instruction_decoded_i
                    && (decoded_subwarp_id_i == i[SubwarpIdWidth-1:0]))
                begin : decoded
                    if (is_branch_i) begin : is_branch
                        // TODO
                    end
                    else begin : normal_instruction
                        // Update PC to next PC
                        pc_act_mask_d[i].pc = next_pc_i;
                        // We are ready again for fetching
                        pc_ready_d[i] = 1'b1;
                    end
                end : decoded
            end : loop_pcs
        end : normal_operation
    end : main_logic

    // PCs are ready for fetching if they are ready and not waiting for a sync
    assign ready_for_fetch = pc_ready_q & (~sync_waiting_q);

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

    // #######################################################################################
    // # Sequential Logic                                                                    #
    // #######################################################################################

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

        assert property (@(posedge clk_i) disable iff (!rst_ni) instruction_decoded_i
                                        |-> pc_act_mask_q[decoded_subwarp_id_i].active_mask != '0)
            else $error("ITS: Instruction decoded but no active threads for subwarp!");

    `endif
endmodule : warp_its_unit
