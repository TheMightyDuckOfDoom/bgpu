// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "common_cells/registers.svh"

/// Reconvergence stack for a single warp
module reconvergence_stack #(
    /// Width of the Program Counter
    parameter int unsigned PcWidth = 32,
    /// Number of threads per warp -> we need log2(WarpWidth) entries
    parameter int unsigned WarpWidth = 32,

    /// Dependent parameter, do **not** overwrite.
    parameter type pc_t       = logic [  PcWidth-1:0],
    parameter type act_mask_t = logic [WarpWidth-1:0]
) (
    /// Clock and reset
    input logic clk_i,
    input logic rst_ni,

    // Initialization
    input logic init_i,
    input pc_t  init_pc_i,

    // To / From Fetcher
    input  logic selected_for_fetch_i,
    output logic ready_for_fetch_o,
    output pc_t  fetch_pc_o,

    // From Decoder
    input logic instruction_decoded_i,
    input logic is_branch_i,
    input pc_t  next_pc_or_reconvergence_pc_i
);
    // #######################################################################################
    // # Local Parameters                                                                    #
    // #######################################################################################

    // Number of entries in the stack
    localparam int unsigned StackEntries = WarpWidth > 1 ? $clog2(WarpWidth) : 1;

    // Stack entry pointer width
    localparam int unsigned StackPtrWidth = $clog2(StackEntries);

    // #######################################################################################
    // # Typedefs                                                                            #
    // #######################################################################################

    // Stack entry type
    typedef struct packed {
        pc_t       pc;               // Current Program Counter
        act_mask_t active_mask;      // Threads that are active
        pc_t       reconvergence_pc; // PC where we reconverge / pop the stack entry
    } stack_entry_t;

    // Stack entry pointer type
    typedef logic [StackPtrWidth-1:0] stack_ptr_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Ready for fetching
    logic ready_for_fetch_d, ready_for_fetch_q;

    // Reconvergence stack entries
    stack_entry_t [StackEntries-1:0] stack_d, stack_q;

    // Stack pointer
    stack_ptr_t stack_ptr_d, stack_ptr_q;

    // Next PC is at the reconvergence point
    logic next_pc_is_reconvergence;

    // #######################################################################################
    // # Combinatorial Logic                                                                 #
    // #######################################################################################

    // Check if the next PC is at the reconvergence point, only if there are multiple entries in the stack
    assign next_pc_is_reconvergence = (stack_ptr_q != '0)
                        && (next_pc_or_reconvergence_pc_i == stack_q[stack_ptr_q].reconvergence_pc);

    // Stack logic
    always_comb begin : stack_logic
        // Default
        stack_d     = stack_q;
        stack_ptr_d = stack_ptr_q;

        ready_for_fetch_d = ready_for_fetch_q;

        // Initialize the stack
        if (init_i) begin : init_stack
            // Clear the stack
            stack_d = '0;

            // Set the first stack entry
            stack_d[0].pc               = init_pc_i; // Initial PC
            stack_d[0].active_mask      = '1;        // All threads as active

            // Reset the stack pointer
            stack_ptr_d = '0;

            // We are ready for fetching
            ready_for_fetch_d = 1'b1;
        end : init_stack

        // Normal operation
        else begin : normal_stack
            // We got selected for fetching -> disable ready for fetching
            if(selected_for_fetch_i) begin : fetch_selected
                ready_for_fetch_d = 1'b0;
            end : fetch_selected

            // We are not ready for fetching anymore
            // Wait until the instruction got decoded
            if(!ready_for_fetch_q && instruction_decoded_i) begin : instruction_decoded
                // If it is not a branch
                if(!is_branch_i) begin : normal_instruction
                    // Check if we reached the reconvergence point
                    if(next_pc_is_reconvergence) begin : reconvergence_point
                        // Pop the stack entry -> decrement the stack pointer
                        stack_ptr_d = stack_ptr_q - 'd1;
                    end : reconvergence_point
                    // Normal instruction -> update the PC of the current stack entry
                    else begin : update_pc
                        // Update the PC of the current stack entry
                        stack_d[stack_ptr_q].pc = next_pc_or_reconvergence_pc_i;
                    end : update_pc

                    // We are ready for fetching again
                    ready_for_fetch_d = 1'b1;
                end : normal_instruction
            end : instruction_decoded
        end : normal_stack
    end : stack_logic

    // #######################################################################################
    // # Outputs                                                                             #
    // #######################################################################################

    // Ready for fetching
    assign ready_for_fetch_o = ready_for_fetch_q;
    // Next PC for fetching -> PC of the current stack entry
    assign fetch_pc_o        = stack_q[stack_ptr_q].pc;

    // #######################################################################################
    // # Sequential Logic                                                                    #
    // #######################################################################################

    // Ready for fetching
    `FF(ready_for_fetch_q, ready_for_fetch_d, '0, clk_i, rst_ni)

    // Stack entries
    `FF(stack_q, stack_d, '0, clk_i, rst_ni)

    // Stack pointer
    `FF(stack_ptr_q, stack_ptr_d, '0, clk_i, rst_ni)

    // #######################################################################################
    // # Assertions                                                                          #
    // #######################################################################################
    `ifndef SYNTHESIS
        // We can never be selected for fetching if we are not ready
        assert property (@(posedge clk_i) disable iff (!rst_ni) selected_for_fetch_i
                                                                    |-> ready_for_fetch_q)
            else $error("Reconvergence stack: Selected for fetching but not ready!");

        // We can never be decoded if we are ready
        assert property (@(posedge clk_i) disable iff (!rst_ni) instruction_decoded_i
                                                                    |-> !ready_for_fetch_q)
            else $error("Reconvergence stack: Instruction decoded but ready for fetching!");
    `endif

endmodule : reconvergence_stack
