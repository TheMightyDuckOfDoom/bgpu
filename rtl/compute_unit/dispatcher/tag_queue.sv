// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "common_cells/registers.svh"

/// Tag Queue
// Gives out unique tags until all tags are used.
// Tags can be freed again, and the queue will give out the next available tag.
module tag_queue #(
    parameter int unsigned NumTags = 8,

    /// Dependent parameter, do **not** overwrite.
    parameter int unsigned TagWidth = $clog2(NumTags),
    parameter type         tag_t    = logic [TagWidth-1:0]
) (
    /// Clock and Reset
    input  logic clk_i,
    input  logic rst_ni,

    input  logic free_i,
    input  tag_t tag_i,

    input  logic get_i,
    output logic valid_o,
    output tag_t tag_o
);

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    logic [NumTags-1:0] tags_used_q, tags_used_d;

    // #######################################################################################
    // # Combinational Logic                                                                 #
    // #######################################################################################

    always_comb begin : comb_logic
        // Default
        tags_used_d = tags_used_q;
        tag_o       = '0;

        // Free
        if (free_i) begin
            tags_used_d[tag_i] = 1'b0;
        end

        // Get handshake
        if (get_i && valid_o) begin
            // Find first unused tag
            for (int i=0; i<NumTags; i++) begin
                if (!tags_used_q[i]) begin
                    tags_used_d[i] = 1'b1;
                    tag_o = i[TagWidth-1:0];
                    break;
                end
            end
        end
    end : comb_logic

    // Output is valid if not all tags are used
    assign valid_o = tags_used_q != '1;

    // #######################################################################################
    // # Squential Logic                                                                     #
    // #######################################################################################

    `FF(tags_used_q, tags_used_d, '0, clk_i, rst_ni)

    // #######################################################################################
    // # Assertions                                                                          #
    // #######################################################################################

    `ifndef SYNTHESIS
        initial assert (NumTags > 1) else $error("NumTags must be greater than 1");

        assert property (@(posedge clk_i) disable iff (!rst_ni) free_i |-> tags_used_q[tag_i])
        else $error("Freeing Tag %d but it is not used! (%0b)", tag_i, tags_used_q);
    `endif

endmodule
