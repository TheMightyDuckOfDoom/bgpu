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

    /// Dependent parameter, do **not** overwrite.
    parameter int unsigned WidWidth   = NumWarps > 1 ? $clog2(NumWarps) : 1,
    parameter type         wid_t      = logic [ WidWidth-1:0],
    parameter type         pc_t       = logic [  PcWidth-1:0],
    parameter type         act_mask_t = logic [WarpWidth-1:0]
) (
    /// Clock and reset
    input logic clk_i,
    input logic rst_ni,

    /// Set Ready status
    input logic set_ready_i,

    /// Which warps are still active or have stopped?
    output logic [NumWarps-1:0] warp_active_o,
    output logic [NumWarps-1:0] warp_stopped_o,

    /// From decode stage |-> is the instruction a branch or update normally to next instruction?
    input logic instruction_decoded_i,
    input logic decode_stop_warp_i,
    input wid_t decode_wid_i,
    input pc_t  decode_next_pc_i,

    /// To/From Fetcher
    input  logic      [NumWarps-1:0] warp_selected_i,
    output logic      [NumWarps-1:0] warp_ready_o,
    output pc_t       [NumWarps-1:0] warp_pc_o,
    output act_mask_t [NumWarps-1:0] warp_act_mask_o
);
    // #######################################################################################
    // # Typedefs                                                                            #
    // #######################################################################################

    // Data per warp stored in the reconvergence stack
    typedef struct packed {
        logic active;
        logic stopped;
        logic ready;
        pc_t pc;
        act_mask_t act_mask;
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

        // Set ready status
        if (set_ready_i) begin
            for(int i = 0; i < NumWarps; i++) begin
                warp_data_d[i].active   = 1'b1;
                warp_data_d[i].ready    = 1'b1;
                warp_data_d[i].act_mask = '1;
            end
        end

        // Did we get an update from decode?
        if (instruction_decoded_i) begin : decode_update

            // Adjust the PC of the decoded warp
            warp_data_d[decode_wid_i].pc = decode_next_pc_i;
            // Mark the warp as ready
            warp_data_d[decode_wid_i].ready = 1'b1;

            // If the warp is finished |-> mark if as stopped
            if (decode_stop_warp_i) begin
                warp_data_d[decode_wid_i].stopped = 1'b1;
                warp_data_d[decode_wid_i].active = 1'b0;
                warp_data_d[decode_wid_i].ready = 1'b0;
            end

        end : decode_update

        for(int i = 0; i < NumWarps; i++) begin : select_update
            // If the warp is selected for fetching, mark it as not ready |-> wait until decode stage
            if (warp_selected_i[i])
                warp_data_d[i].ready = 1'b0;

        end : select_update
    end : next_pc_ready_logic

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
        assign warp_active_o  [i] = warp_data_q[i].active;
        assign warp_stopped_o [i] = warp_data_q[i].stopped;
        assign warp_ready_o   [i] = warp_data_q[i].ready && warp_data_q[i].active
            && (|warp_data_q[i].act_mask);
        assign warp_pc_o      [i] = warp_data_q[i].pc;
        assign warp_act_mask_o[i] = warp_data_q[i].act_mask;
    end : gen_assign_outputs

    // #######################################################################################
    // # Asserts                                                                             #
    // #######################################################################################

    `ifndef SYNTHESIS
        for (genvar i = 0; i < NumWarps; i++) begin : gen_asserts
            // Check that a ready warp has at least one active thread |-> otherwise we waste resources
            assert property (@(posedge clk_i) disable iff (!rst_ni)
                (!warp_ready_o[i] || (warp_ready_o[i] && warp_act_mask_o[i] != '0
                && !warp_stopped_o[i])))
            else $error("Warp is marked as ready, but no thread is active");

            assert property (@(posedge clk_i) disable iff (!rst_ni)
                (warp_selected_i[i] |-> warp_data_q[i].active))
            else $error("Warp was selected for fetching, but is not active: %0d", i);

            assert property (@(posedge clk_i) disable iff (!rst_ni)
                (warp_selected_i[i] |-> warp_data_q[i].ready && !warp_data_q[i].stopped
                && (|warp_data_q[i].act_mask)))
            else $error("Warp was selected for fetching, but is not ready: %0d", i);

            assert property (@(posedge clk_i) disable iff (!rst_ni)
                (warp_selected_i[i] |-> !warp_data_q[i].stopped && (|warp_data_q[i].act_mask)))
            else $error("Warp was selected for fetching, but is stopped: %0d", i);

            assert property (@(posedge clk_i) disable iff (!rst_ni)
                (warp_selected_i[i] |-> |warp_data_q[i].act_mask))
            else $error("Warp was selected for fetching, but active mask is zero: %0d", i);

        end : gen_asserts

        // A warp cannot be selected and be decoded at the same time
        assert property (@(posedge clk_i) disable iff (!rst_ni)
            (instruction_decoded_i |-> !warp_selected_i[decode_wid_i]))
        else $error("Warp was selected for fetching, but got decoded at the same time: %0d",
            decode_wid_i);

        // Check that a warp that was decoded is active
        assert property (@(posedge clk_i) disable iff (!rst_ni)
            instruction_decoded_i |-> warp_data_q[decode_wid_i].active)
        else $error("Warp was decoded, but is not active: %0d", decode_wid_i);

        // Check that a warp that was decoded is not ready
        assert property (@(posedge clk_i) disable iff (!rst_ni)
            instruction_decoded_i |-> !warp_data_q[decode_wid_i].ready)
        else $error("Warp was decoded, but is ready: %0d", decode_wid_i);

        // Check that a warp that was decoded is not stopped
        assert property (@(posedge clk_i) disable iff (!rst_ni)
            instruction_decoded_i |-> !warp_data_q[decode_wid_i].stopped)
        else $error("Warp was decoded, but is stopped: %0d", decode_wid_i);
    `endif

endmodule : dummy_reconvergence_stack
