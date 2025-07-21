// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Dummy Reconvergence Stack
/// When a warp is selected for fetching, its marked as not ready
/// until it has passed the decode stage, where we know if it just was a normal instruction or a branch
/// But as this is a dummy implementation, it just increments the PC to the next instruction

`include "common_cells/registers.svh"

module dummy_reconvergence_stack #(
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
    parameter int unsigned WidWidth = NumWarps > 1 ? $clog2(NumWarps) : 1,
    parameter type tblock_idx_t = logic [TblockIdxBits-1:0],
    parameter type tblock_id_t  = logic [ TblockIdBits-1:0],
    parameter type addr_t       = logic [ AddressWidth-1:0],
    parameter type wid_t        = logic [     WidWidth-1:0],
    parameter type pc_t         = logic [      PcWidth-1:0],
    parameter type act_mask_t   = logic [    WarpWidth-1:0]
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
    input logic instruction_decoded_i,
    input logic decode_stop_warp_i,
    input wid_t decode_wid_i,
    input pc_t  decode_next_pc_i,

    /// From instruction buffer
    // Are there any instructions in flight?
    input  logic [NumWarps-1:0] ib_all_instr_finished_i,

    /// To/From Fetcher
    input  logic      [NumWarps-1:0] warp_selected_i,
    output logic      [NumWarps-1:0] warp_ready_o,
    output pc_t       [NumWarps-1:0] warp_pc_o,
    output act_mask_t [NumWarps-1:0] warp_act_mask_o,

    /// To Integer Unit
    output addr_t       [NumWarps-1:0] warp_dp_addr_o,   // Data / Parameter address
    output tblock_idx_t [NumWarps-1:0] warp_tblock_idx_o // Block index
);
    // #######################################################################################
    // # Typedefs                                                                            #
    // #######################################################################################

    // Data per warp stored in the reconvergence stack
    typedef struct packed {
        logic        occupied;
        logic        finished;
        logic        ready;
        pc_t         pc;
        act_mask_t   act_mask;
        addr_t       dp_addr;    // Data / Parameter address
        tblock_idx_t tblock_idx; // Block index -> used to calculate the thread id
        tblock_id_t  tblock_id;  // Unique identifier for the block
    } warp_data_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Reconvergence stack data
    warp_data_t [NumWarps-1:0] warp_data_q, warp_data_d;

    // #######################################################################################
    // # Combinatorial Logic                                                                 #
    // #######################################################################################

    // Next PC and ready logic
    always_comb begin : next_pc_ready_logic
        // Default
        warp_data_d[NumWarps-1:0] = warp_data_q[NumWarps-1:0];

        tblock_done_o = 1'b0;
        tblock_done_id_o = '0;

        // Allocate a new warp
        if (allocate_warp_i && warp_free_o) begin : allocate_warp
            // Find the first free warp
            for(int i = 0; i < NumWarps; i++) begin : find_free_warp
                if (!warp_data_q[i].occupied) begin
                    // Allocate the warp
                    warp_data_d[i].occupied   = 1'b1;
                    warp_data_d[i].finished   = 1'b0;
                    warp_data_d[i].ready      = 1'b1; // Can start fetching immediately
                    warp_data_d[i].act_mask   = '1; // All threads are active at the start
                    warp_data_d[i].pc         = allocate_pc_i;
                    warp_data_d[i].tblock_idx = allocate_tblock_idx_i;
                    warp_data_d[i].tblock_id  = allocate_tblock_id_i;
                    warp_data_d[i].dp_addr    = allocate_dp_addr_i;
                    break;
                end
            end : find_free_warp
        end

        // Did we get an update from decode?
        if (instruction_decoded_i) begin : decode_update

            // Adjust the PC of the decoded warp
            warp_data_d[decode_wid_i].pc = decode_next_pc_i;
            // Mark the warp as ready
            warp_data_d[decode_wid_i].ready = 1'b1;

            // If the warp is finished |-> mark it as finished,
            // wait until all instructions are finished
            if (decode_stop_warp_i) begin
                warp_data_d[decode_wid_i].finished = 1'b1;
                warp_data_d[decode_wid_i].ready    = 1'b0;
            end

        end : decode_update

        for(int i = 0; i < NumWarps; i++) begin : update
            // If the warp is selected for fetching, mark it as not ready |-> wait until decode stage
            if (warp_selected_i[i]) begin
                warp_data_d[i].ready = 1'b0;
            end

            // If the warp is finished and all instructions are finished |-> deallocate the warp and notify
            if (warp_data_q[i].occupied && warp_data_q[i].finished
                && ib_all_instr_finished_i[i] && (!tblock_done_o)) begin

                tblock_done_o    = 1'b1;
                tblock_done_id_o = warp_data_q[i].tblock_id;

                // Deallocate the warp upon handshake
                if (tblock_done_ready_i) begin
                    warp_data_d[i].occupied = 1'b0;
                    warp_data_d[i].ready    = 1'b0;
                    warp_data_d[i].finished = 1'b0;
                end
            end
        end : update
    end : next_pc_ready_logic

    // We can allocate a new warp if there is at least one warp that is not active
    always begin : warp_free
        warp_free_o = 1'b0;
        for(int i = 0; i < NumWarps; i++) begin : check
            if(!warp_data_q[i].occupied) begin
                warp_free_o = 1'b1;
            end
        end
    end : warp_free

    // #######################################################################################
    // # Sequential Logic                                                                    #
    // #######################################################################################

    for(genvar i = 0; i < NumWarps; i++) begin : gen_ff
        `FF(warp_data_q[i], warp_data_d[i], '0, clk_i, rst_ni)
    end : gen_ff

    // #######################################################################################
    // # Outputs                                                                             #
    // #######################################################################################

    for(genvar i = 0; i < NumWarps; i++) begin : gen_assign_outputs
        assign warp_ready_o     [i] = warp_data_q[i].ready && warp_data_q[i].occupied
            && (|warp_data_q[i].act_mask);
        assign warp_pc_o        [i] = warp_data_q[i].pc;
        assign warp_act_mask_o  [i] = warp_data_q[i].act_mask;
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
                (warp_selected_i[i] |-> warp_data_q[i].ready
                && (|warp_data_q[i].act_mask)))
            else $error("Warp was selected for fetching, but is not ready: %0d", i);

            assert property (@(posedge clk_i) disable iff (!rst_ni)
                (warp_selected_i[i] |-> (|warp_data_q[i].act_mask)))
            else $error("Warp was selected for fetching, but is no thread is active: %0d", i);

            assert property (@(posedge clk_i) disable iff (!rst_ni)
                (warp_selected_i[i] |-> |warp_data_q[i].act_mask))
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

        // Check that a warp that was decoded is not ready
        assert property (@(posedge clk_i) disable iff (!rst_ni)
            instruction_decoded_i |-> !warp_data_q[decode_wid_i].ready)
        else $error("Warp was decoded, but is ready: %0d", decode_wid_i);
    `endif

endmodule : dummy_reconvergence_stack
