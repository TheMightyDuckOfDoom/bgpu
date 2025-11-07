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
        assert_valid_only_when_available:
            assert property (@(posedge clk_i) !valid_o | (tags_used_q != '1))
            else $error("valid_o is high but no tags are available! (%0b)", tags_used_q);

        // Given tag must be currently unused
        assert_tag_unused_when_valid:
            assert property (@(posedge clk_i) disable iff (!rst_ni) !valid_o || !tags_used_q[tag_o])
            else $error("Giving out an already used tag: %0d", tag_o);

        // After a tag is given out, it must be marked as used
        assert_mark_as_used:
            assert property (@(posedge clk_i) disable iff (!rst_ni) !(valid_o && get_i)
                || tags_used_d[tag_o])
            else $error("Tag %0d is given out but not marked as used!", tag_o);

        // We can only free used tags
        assert_only_free_unused_tags:
            assert property (@(posedge clk_i) disable iff (!rst_ni) !free_i
                || tags_used_q[tag_i])
            else $error("Trying to free an unused tag: %0d", tag_i);

        // After a tag is freed, it must be marked as unused
        assert_mark_as_unused:
            assert property (@(posedge clk_i) disable iff (!rst_ni) !free_i
                || !tags_used_d[tag_i])
            else $error("Tag %0d is freed but not marked as unused!", tag_i);
    `endif

    // #######################################################################################
    // # Formal Properties                                                                   #
    // #######################################################################################

    `ifdef FORMAL
        // All tags are free
        cover_all_free:
            cover property (@(posedge clk_i) disable iff (!rst_ni) tags_used_q == '0);

        // All tags are used
        cover_all_used:
            cover property (@(posedge clk_i) disable iff (!rst_ni) tags_used_q == '1);

        // Try to get a tag when all are used
        cover_get_when_all_used:
            cover property (@(posedge clk_i) disable iff (!rst_ni) get_i && (tags_used_q == '1));

        // Try to get and free a tag at the same time
        cover_get_and_free:
            cover property (@(posedge clk_i) disable iff (!rst_ni) get_i && free_i);

        // Cover that we actually get a tag
        cover_get_handshake:
            cover property (@(posedge clk_i) disable iff (!rst_ni) valid_o && get_i);

        // Cover that we free a tag
        cover_free:
            cover property (@(posedge clk_i) disable iff (!rst_ni) free_i);

        // Cover that we have a tag available
        cover_valid:
            cover property (@(posedge clk_i) disable iff (!rst_ni) valid_o);

        // Cover that we do not have a tag available
        cover_invalid:
            cover property (@(posedge clk_i) disable iff (!rst_ni) !valid_o);

        // Can only free used tags
        assume_only_free_unused_tags:
            assume property (@(posedge clk_i) disable iff (!rst_ni) free_i == tags_used_q[tag_i]);
    `endif

endmodule : tag_queue
