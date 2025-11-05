// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "common_cells/registers.svh"

/// Tag Queue
// Gives out unique tags until all tags are used.
// Tags can be freed again, and the queue will give out the next available tag.
module tag_queue #(
    /// Number of tags that can be given out.
    parameter int unsigned NumTags = 8,

    /// Dependent parameter, do **not** overwrite.
    parameter int unsigned TagWidth = $clog2(NumTags),
    parameter type         tag_t    = logic [TagWidth-1:0]
) (
    /// Clock and Reset
    input  logic clk_i,
    input  logic rst_ni,

    /// Freeing
    input  logic free_i,
    input  tag_t tag_i,

    /// Getting
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

    // Find free tag
    always_comb begin : find_free_tag
        tag_o = '0;
        for (int i = 0; i < NumTags; i++) begin
            if (!tags_used_q[i]) begin
                tag_o = i[TagWidth-1:0];
                break;
            end
        end
    end : find_free_tag

    // Determine used tags
    always_comb begin : tag_logic
        // Default
        tags_used_d = tags_used_q;

        // Free
        if (free_i) begin
            tags_used_d[tag_i] = 1'b0;
        end

        // Get handshake
        if (get_i && valid_o) begin
            tags_used_d[tag_o] = 1'b1;
        end
    end : tag_logic

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
        // Parameter sanity check
        initial assert (NumTags > 1) else $error("NumTags must be greater than 1");

        // Valid output only when tags are available
        assert property (@(posedge clk_i) !valid_o | (tags_used_q != '1))
            else $error("valid_o is high but no tags are available! (%0b)", tags_used_q);

        // Given tag must be currently unused
        assert property (@(posedge clk_i) !(valid_o && rst_ni) || (tags_used_q[tag_o] == 1'b0))
            else $error("Giving out an already used tag: %0d", tag_o);

        // After a tag is given out, it must be marked as used
        assert property (@(posedge clk_i) !($past(valid_o && get_i && rst_ni) && rst_ni) ||
            (tags_used_q[$past(tag_o)] == 1'b1))
            else $error("Tag %0d was given out but not marked as used!", $past(tag_o));

        // We can only free used tags
        assert property (@(posedge clk_i) !(free_i & rst_ni) || (tags_used_q[tag_i] == 1'b1))
            else $error("Trying to free an unused tag: %0d", tag_i);

        // After a tag is freed, it must be marked as unused
        assert property (@(posedge clk_i) !($past(free_i && rst_ni) && rst_ni)
            || (tags_used_q[$past(tag_i)] == 1'b0))
            else $error("Tag %0d was freed but not marked as unused!", $past(tag_i));
    `endif

    // #######################################################################################
    // # Formal Properties                                                                   #
    // #######################################################################################

    `ifdef FORMAL
        // All tags are free
        cover property (@(posedge clk_i) disable iff (!rst_ni) tags_used_q == '0);

        // All tags are used
        cover property (@(posedge clk_i) disable iff (!rst_ni) tags_used_q == '1);

        // Try to get a tag when all are used
        cover property (@(posedge clk_i) disable iff (!rst_ni) get_i && (tags_used_q == '1));

        // Try to get and free a tag at the same time
        cover property (@(posedge clk_i) disable iff (!rst_ni) get_i && free_i);

        // Can only free used tags
        assume property (@(posedge clk_i) disable iff (!rst_ni) free_i == tags_used_q[tag_i]);

        // Reset at beginning
        fv_reset #(
            .RESET_CYCLES( 1 )
        ) i_fv_reset (
            .clk_i ( clk_i  ),
            .rst_ni( rst_ni )
        );
    `endif

endmodule : tag_queue
