// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// BGPU Wrapper for Gowin FPGAs
// Contains:
// - PLL for Clock Generation
// - Reset Synchronization
// - BGPU SoC
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
    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // PLL locked
    logic pll_locked;

    // System Reset Request
    logic rst_sys_req_n;

    // System Clock and reset
    logic clk_sys, rst_sys_n;

    // #######################################################################################
    // # PLL                                                                                 #
    // #######################################################################################

    // 50Mhz External Clock to 40Mhz System Clock
    Gowin_PLL_50m_to_40m i_pll (
        .init_clk( clk_i      ),
        .clkin   ( clk_i      ),
        .clkout0 ( clk_sys    ),
        .reset   ( !rst_ni    ),
        .lock    ( pll_locked )
    );

    // #######################################################################################
    // # Reset Synchronizer                                                                  #
    // #######################################################################################

    // Reset Requested by external reset or while the PLL is not locked
    assign rst_sys_req_n = rst_ni && pll_locked;

    // Reset Synchronization to the system clock
    rstgen_bypass #(
        .NumRegs( 4 )
    ) i_rstgen (
        .clk_i           ( clk_sys       ),
        .rst_ni          ( rst_sys_req_n ),
        .rst_test_mode_ni( rst_sys_req_n ),
        .test_mode_i     ( 1'b0          ),
        .rst_no          ( rst_sys_n     ),
        .init_no         ( /* Unused */  )
    );

    // #######################################################################################
    // # BGPU SoC                                                                            #
    // #######################################################################################

    bgpu_soc i_bgpu (
        .clk_i ( clk_sys   ),
        .rst_ni( rst_sys_n ),

        .testmode_i ( 1'b0 ),

        .jtag_tck_i  ( jtag_tck_i   ),
        .jtag_tdi_i  ( jtag_tdi_i   ),
        .jtag_tdo_o  ( jtag_tdo_o   ),
        .jtag_tms_i  ( jtag_tms_i   ),
        .jtag_trst_ni( jtag_trst_ni )
    );

endmodule : bgpu_wrapper
