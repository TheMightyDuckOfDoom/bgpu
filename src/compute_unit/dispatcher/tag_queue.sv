// Copyright March 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "common_cells/registers.svh"

module tag_queue #(
    parameter int NumTags = 8,

    /// Dependent parameter, do **not** overwrite.
    parameter int TagWidth = $clog2(NumTags),
    parameter type tag_t   = logic [TagWidth-1:0]
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

    logic [NumTags-1:0] tags_used_q, tags_used_d;

    assign valid_o = !(&tags_used_q);

    always_comb begin
        // Default
        tags_used_d = tags_used_q;
        tag_o = '0;

        // Free
        if(free_i) begin
            assert(tags_used_q[tag_i])
            else $error("Tag %d not in tag queue", tag_i);

            tags_used_d[tag_i] = 1'b0;
        end    

        // Get
        if(get_i && valid_o) begin
            for(int i=0; i<NumTags; i++) begin
                if(!tags_used_q[i]) begin
                    tags_used_d[i] = 1'b1;
                    tag_o = i[TagWidth-1:0];
                    break;
                end
            end
        end
    end

    `FF(tags_used_q, tags_used_d, '0, clk_i, rst_ni);

    `ifndef SYNTHESIS
        // Tags in flight queue
        logic [NumTags-1:0] inflight_queue_d, inflight_queue_q;

        always @(posedge clk_i) begin
            if(!rst_ni) begin
                inflight_queue_q <= '0;
            end else begin
                inflight_queue_q <= inflight_queue_d;
            end
        end

        always_comb begin
            inflight_queue_d = inflight_queue_q;

            // Read from queue -> add to inflight queue
            if (get_i && valid_o) begin
                // Check that the tag is not already in the queue
                if(inflight_queue_q[tag_o])
                    $display("Tag %d already in inflight queue", tag_o);

                inflight_queue_d[tag_o] = 1'b1;
            end

            // Write to queue -> remove from inflight queue
            if (free_i) begin
                // Make sure that tag is in the queue
                if(!inflight_queue_q[tag_i])
                    $display("Tag %d not in inflight queue", tag_i);
                inflight_queue_d[tag_i] = 1'b0;
            end
        end
    `endif

endmodule
