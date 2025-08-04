// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Wrapper for the BGPU SoC to be used with Gowin FPGAs.
module bgpu_wrapper (
    // Clock and reset
    input logic clk_i,
    input logic rst_ni,

    input logic testmode_i,

    /// JTAG interface
    input  logic jtag_tck_i,
    input  logic jtag_tdi_i,
    output logic jtag_tdo_o,
    input  logic jtag_tms_i,
    input  logic jtag_trst_ni
);
    logic clk30, locked;
    logic [3:0] rst_synced_q;

    Gowin_PLL_50_to_30(
        .clkin   ( clk_i   ),
        .clkout0 ( clk30   ),
        .init_clk( clk_i   ),
        .lock    ( locked  ),
        .reset   ( !rst_ni )
    );

    initial rst_synced_q = '0;
    always_ff @(posedge clk30) begin
        rst_synced_q[0] <= rst_ni & locked;
        rst_synced_q[1] <= rst_synced_q[0];
        rst_synced_q[2] <= rst_synced_q[1];
        rst_synced_q[3] <= rst_synced_q[2];
    end

    bgpu_soc i_bgpu_soc (
        .clk_i     ( clk30           ),
        .rst_ni    ( rst_synced_q[3] ),
        .testmode_i( testmode_i      ),

        .jtag_tck_i  ( jtag_tck_i   ),
        .jtag_tdi_i  ( jtag_tdi_i   ),
        .jtag_tdo_o  ( jtag_tdo_o   ),
        .jtag_tms_i  ( jtag_tms_i   ),
        .jtag_trst_ni( jtag_trst_ni )
    );

endmodule : bgpu_wrapper
