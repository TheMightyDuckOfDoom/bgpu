// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Wrapper for the BGPU SoC to be used with Gowin FPGAs.
module bgpu_wrapper (
    // Clock and reset
    input logic clk_i,
    input logic rst_ni,

    /// JTAG interface
    input  logic jtag_tck_i,
    input  logic jtag_tdi_i,
    output logic jtag_tdo_o,
    input  logic jtag_tms_i,
    input  logic jtag_trst_ni
);
    bgpu_soc i_bgpu_soc (
        .clk_i     ( clk_i  ),
        .rst_ni    ( rst_ni ),
        .testmode_i( 1'b0   ),

        .jtag_tck_i  ( jtag_tck_i   ),
        .jtag_tdi_i  ( jtag_tdi_i   ),
        .jtag_tdo_o  ( jtag_tdo_o   ),
        .jtag_tms_i  ( jtag_tms_i   ),
        .jtag_trst_ni( jtag_trst_ni )
    );
endmodule : bgpu_wrapper
