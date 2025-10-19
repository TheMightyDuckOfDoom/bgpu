// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "common_cells/registers.svh"

/// Tag Queue
// Gives out unique tags until all tags are used.
// Tags can be freed again, and the queue will give out the next available tag.
module tag_queue #(
    /// Number of tags that can be given out
    parameter int unsigned NumTags   = 8,
    /// Number of tags that can be given out at once
    parameter int unsigned NumTagOut = 2,
    /// Number of tags that can be freed at once
    parameter int unsigned NumTagIn = 2,

    /// Dependent parameter, do **not** overwrite.
    parameter int unsigned TagWidth = $clog2(NumTags),
    parameter type         tag_t    = logic [TagWidth-1:0]
) (
    /// Clock and Reset
    input  logic clk_i,
    input  logic rst_ni,

    input  logic [NumTagIn-1:0] free_i,
    input  tag_t [NumTagIn-1:0] tag_i,

    input  logic [NumTagOut-1:0] get_i,
    output logic [NumTagOut-1:0] valid_o,
    output tag_t [NumTagOut-1:0] tag_o
);

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    logic [NumTags-1:0] tags_used_q, tags_used_d;
    logic [NumTags-1:0] tags_used_tmp;

    // #######################################################################################
    // # Combinational Logic                                                                 #
    // #######################################################################################

    // Find free tag
    always_comb begin : find_free_tag
        tag_o = '0;
        valid_o = '0;
        tags_used_tmp = tags_used_q;
        for (int out_idx = 0; out_idx < NumTagOut; out_idx++) begin : loop_out_tags
            for (int i = 0; i < NumTags; i++) begin : loop_find_tag
                if (!tags_used_tmp[i]) begin
                    tag_o  [out_idx] = i[TagWidth-1:0];
                    valid_o[out_idx] = 1'b1;
                    tags_used_tmp[i] = 1'b1;
                    break;
                end
            end : loop_find_tag
        end : loop_out_tags
    end : find_free_tag

    // Determine used tags
    always_comb begin : tag_logic
        // Default
        tags_used_d = tags_used_q;

        // Free
        for (int j = 0; j < NumTagIn; j++) begin : loop_in_width
            if (free_i[j]) begin : free_tag
                tags_used_d[tag_i[j]] = 1'b0;
            end : free_tag
        end : loop_in_width

        // Give out multiple tags
        for (int out_idx = 0; out_idx < NumTagOut; out_idx++) begin : loop_out_width
            // Mark tag as used if it is given out
            if (get_i[out_idx] && valid_o[out_idx]) begin : mark_used
                tags_used_d[tag_o[out_idx]] = 1'b1;
            end : mark_used
        end : loop_out_width
    end : tag_logic

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
        initial assert (NumTagOut >= 1) else $error("NumTagOut must be at least 1");
        initial assert (NumTagIn  >= 1) else $error("NumTagIn must be at least 1");

        // Output assertions
        for (genvar out_idx = 0; out_idx < NumTagOut; out_idx++) begin : loop_out_asserts
            // Valid output only when tags are available
            if (out_idx == 0) begin : assert_valid_only_when_available
                assert property (@(posedge clk_i) !valid_o[out_idx] | (tags_used_q != '1))
                else $error("%d: valid_o is high but no tags are available! (%0b)", out_idx, tags_used_q);
            end : assert_valid_only_when_available
            else begin
                assert_higher_valid_only_when_lower_valid:
                    assert property (@(posedge clk_i) !valid_o[out_idx] || valid_o[out_idx-1])
                    else $error("%d: valid_o is high but lower index is not valid!", out_idx);
            end

            // No two tags the same
            for (genvar other_idx = 0; other_idx < NumTagOut; other_idx++) begin : assert_unique_tags
                if (other_idx != out_idx) begin : if_other_idx
                    assert property (@(posedge clk_i) !(valid_o[out_idx] && valid_o[other_idx])
                        || (tag_o[out_idx] != tag_o[other_idx]))
                    else $error("%d and %d: Same tag given out twice: %0d", out_idx, other_idx, tag_o[out_idx]);
                end : if_other_idx
            end : assert_unique_tags

            // Given tag must be currently unused
            assert_tag_unused_when_valid:
                assert property (@(posedge clk_i) disable iff (!rst_ni) !valid_o[out_idx] || !tags_used_q[tag_o[out_idx]])
                else $error("%d: Giving out an already used tag: %0d", out_idx, tag_o[out_idx]);

            // After a tag is given out, it must be marked as used
            assert_mark_as_used:
                assert property (@(posedge clk_i) disable iff (!rst_ni) !(valid_o[out_idx] && get_i[out_idx])
                    || tags_used_d[tag_o[out_idx]])
                else $error("%d: Tag %0d is given out but not marked as used!", out_idx, tag_o[out_idx]);
        end : loop_out_asserts

        // We can only free used tags
        for (genvar in_idx = 0; in_idx < NumTagIn; in_idx++) begin : loop_in_asserts
            assert_only_free_unused_tags:
                assert property (@(posedge clk_i) disable iff (!rst_ni) !free_i[in_idx]
                    || tags_used_q[tag_i[in_idx]])
                else $error("%d: Trying to free an unused tag: %0d", in_idx, tag_i[in_idx]);

            // After a tag is freed, it must be marked as unused
            assert_mark_as_unused:
                assert property (@(posedge clk_i) disable iff (!rst_ni) !free_i[in_idx]
                    || !tags_used_d[tag_i[in_idx]])
                else $error("%d: Tag %0d is freed but not marked as unused!", in_idx, tag_i[in_idx]);
        end : loop_in_asserts
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
        for (genvar out_idx = 0; out_idx < NumTagOut; out_idx++) begin : loop_out_cover_get_when_all_used
            cover_get_when_all_used_idx:
                cover property (@(posedge clk_i) disable iff (!rst_ni) get_i[out_idx] && (tags_used_q == '1));
        end : loop_out_cover_get_when_all_used

        // Try to get and free a tag at the same time
        for (genvar out_idx = 0; out_idx < NumTagOut; out_idx++) begin : loop_out_cover_get_and_free
            for (genvar in_idx = 0; in_idx < NumTagIn; in_idx++) begin : loop_in_width
                cover_get_and_free_idx:
                    cover property (@(posedge clk_i) disable iff (!rst_ni) get_i[out_idx] && free_i[in_idx]);
            end : loop_in_width
        end : loop_out_cover_get_and_free

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
        for (genvar in_idx = 0; in_idx < NumTagIn; in_idx++) begin : loop_in_formal_free
            assume_only_free_unused_tags:
                assume property (@(posedge clk_i) disable iff (!rst_ni) free_i[in_idx] == tags_used_q[tag_i[in_idx]]);
        end : loop_in_formal_free
    `endif

endmodule : tag_queue
