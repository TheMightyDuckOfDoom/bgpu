// Copyright Feb 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Dummy Reconvergence Stack
/// When a warp is selected for fetching, its marked as not ready
/// until it has passed the decode stage, where we know if it just was a normal instruction or a branch
/// But as this is a dummy implementation, it just increments the PC to the next instruction

`include "common_cells/registers.svh"

module dummy_reconvergence_stack #(
    /// Width of the Program Counter
    parameter int PcWidth = 32,
    /// Number of warps per compute unit
    parameter int NumWarps = 32,
    /// Number of threads per warp
    parameter int WarpWidth = 32,

    /// Dependent parameter, do **not** overwrite.
    parameter int  WidWidth   = $clog2(NumWarps),
    parameter type wid_t      = logic [ WidWidth-1:0],
    parameter type pc_t       = logic [  PcWidth-1:0],
    parameter type act_mask_t = logic [WarpWidth-1:0]
) (
    /// Clock and reset
    input logic clk_i,
    input logic rst_ni,

    /// From decode stage -> is the instruction a branch or update normally to next instruction?
    input logic instruction_decoded_i,
    input wid_t decode_wid_i,

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
        logic ready;
        pc_t pc;
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

        // Did we get an update from decode?
        if(instruction_decoded_i) begin : decode_update
            assert(warp_data_q[decode_wid_i].ready == 1'b1)
            else $fatal("Warp was already ready, but got decoded");
            // Increment the PC of the decoded warp
            warp_data_d[decode_wid_i].pc = warp_data_q[decode_wid_i].pc + '1;
            // Mark the warp as ready
            warp_data_d[decode_wid_i].ready = 1'b1;
        end : decode_update

        for(int i = 0; i < NumWarps; i++) begin : select_update
            assert(!instruction_decoded_i || (instruction_decoded_i && warp_selected_i[decode_wid_i] == 0))
            else $fatal("Warp was selected for fetching, but got decoded");

            // If the warp is selected for fetching, increment the PC
            if(warp_selected_i[i]) begin
                assert(warp_data_q[i].ready == 1'b1)
                else $fatal("Warp was not ready, but got selected for fetching");
                assert($onehot(warp_selected_i))
                else $fatal("Multiple warps selected for fetching");
                // Increment the PC of the selected warp
                warp_data_d[i].pc = warp_data_q[i].pc + '1;
            end
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

    for(genvar i = 0; i < NumWarps; i++) begin : assign_outputs
        assign warp_ready_o   [i] = warp_data_q[i].ready;
        assign warp_pc_o      [i] = warp_data_q[i].pc;
        assign warp_act_mask_o[i] = '1; // All warps are active
    end : assign_outputs

endmodule : dummy_reconvergence_stack
