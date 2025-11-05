// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Formal verification module for reset behavior
module fv_reset #(
    parameter int unsigned RESET_CYCLES = 4 
) (
    input logic clk_i,
    input logic rst_ni
);

    localparam int unsigned CntWidth = RESET_CYCLES > 1 ? $clog2(RESET_CYCLES) : 1;

    logic [CntWidth-1:0] reset_cnt_q;
    
    // Initialize reset counter
    initial reset_cnt_q = '0;

    // Reset behavior
    // While reset counter is less than RESET_CYCLES, reset is assumed to be active
    // After that, reset is assumed to be inactive
    always_ff @(posedge clk_i) begin
        if (reset_cnt_q < RESET_CYCLES) begin
            assume(!rst_ni);
            reset_cnt_q <= reset_cnt_q + 1;
        end else begin
            assume(rst_ni);
        end
    end

endmodule : fv_reset
