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
    input  logic jtag_trst_ni,

    /// DDR3 memory interface
    output logic [13:0] ddr_addr_o,
    output logic [ 2:0] ddr_bank_o,
    output logic        ddr_cs_no,
    output logic        ddr_ras_no,
    output logic        ddr_cas_no,
    output logic        ddr_we_no,
    output logic        ddr_ck_o,
    output logic        ddr_ck_o_n,
    output logic        ddr_cke_o,
    output logic        ddr_odt_o,
    output logic        ddr_reset_no,
    output logic [ 3:0] ddr_dm_o,
    inout  logic [ 3:0] ddr_dqs_io,
    inout  logic [ 3:0] ddr_dqs_io_n,
    inout  logic [31:0] ddr_dq_io,

    /// Status LEDs
    output logic status_pll_locked_no,    // PLL is locked
    output logic status_running_no,       // Not reset, i.e. system is running
    output logic status_ddr3_init_done_no, // DDR3 initialization is done
    output logic dummy_o
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

    // DDR3 Controller signals
    logic clk_mctrl;
    logic clk_memory;
    logic ddr3_init_done, stop_memory_clk;

    // #######################################################################################
    // # PLL                                                                                 #
    // #######################################################################################

    // 50Mhz External Clock to 40Mhz System Clock
    Gowin_PLL i_pll (
        .init_clk( clk_i      ), // 50Mhz
        .clkin   ( clk_i      ), // 50Mhz
        .clkout0 ( clk_sys    ), // 40Mhz
        .enclk0  ( 1'b1       ),
        .clkout2 ( clk_memory ), // 400Mhz
        .enclk2  ( stop_memory_clk ), // This seems wrong, but is correct according to Docs
        .reset   ( !rst_ni    ),
        .lock    ( pll_locked )
    );

    assign status_pll_locked_no = !pll_locked;

    // #######################################################################################
    // # Reset                                                                               #
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

    assign status_running_no = !rst_sys_n;

    // #######################################################################################
    // # BGPU SoC                                                                            #
    // #######################################################################################

    bgpu_soc i_bgpu (
        .clk_i ( clk_sys   ),
        .rst_ni( rst_sys_n ),

        .testmode_i( 1'b0 ),

        .mgmt_cpu_clk_i( clk_sys ),

        .jtag_tck_i  ( jtag_tck_i   ),
        .jtag_tdi_i  ( jtag_tdi_i   ),
        .jtag_tdo_o  ( jtag_tdo_o   ),
        .jtag_tms_i  ( jtag_tms_i   ),
        .jtag_trst_ni( jtag_trst_ni )
    );

    // #######################################################################################
    // # Gowin Memory Controller                                                             #
    // #######################################################################################

    DDR3_Memory_Interface_Top i_ddr3_ctrl(
        .clk       ( clk_sys         ),
        .pll_stop  ( stop_memory_clk ),
        .memory_clk( clk_memory      ),
        .pll_lock  ( pll_locked      ),
        .rst_n     ( rst_ni          ),
        .clk_out   ( clk_mctrl       ), // clk_memory / 4
        .ddr_rst   (),

        .init_calib_complete( ddr3_init_done ),

        .burst( 1'b0 ),
        
        // Command Interface
        .cmd_ready(),
        .cmd_en   ( 1'b0 ),
        .cmd      ( '0   ),
        .addr     ( '0   ),
        
        // Write Data Interface
        .wr_data_rdy (),
        .wr_data_en  ( 1'b0 ),
        .wr_data     ( '0   ),
        .wr_data_end ( 1'b0 ),
        .wr_data_mask( '0   ),
        
        // Read Data Interface
        .rd_data_valid(),
        .rd_data_end  (),
        .rd_data      (),

        // Refresh Interface
        .sr_req ( 1'b0 ),
        .sr_ack (),
        .ref_req( 1'b0 ),
        .ref_ack(),

        // DDR3 Interface
        .O_ddr_addr   ( ddr_addr_o   ),
        .O_ddr_ba     ( ddr_bank_o   ),
        .O_ddr_cs_n   ( ddr_cs_no    ),
        .O_ddr_ras_n  ( ddr_ras_no   ),
        .O_ddr_cas_n  ( ddr_cas_no   ),
        .O_ddr_we_n   ( ddr_we_no    ),
        .O_ddr_clk    ( ddr_ck_o     ),
        .O_ddr_clk_n  ( ddr_ck_o_n   ),
        .O_ddr_cke    ( ddr_cke_o    ),
        .O_ddr_odt    ( ddr_odt_o    ),
        .O_ddr_reset_n( ddr_reset_no ),
        .O_ddr_dqm    ( ddr_dm_o     ),
        .IO_ddr_dq    ( ddr_dq_io    ),
        .IO_ddr_dqs   ( ddr_dqs_io   ),
        .IO_ddr_dqs_n ( ddr_dqs_io_n )
    );

    assign status_ddr3_init_done_no = !ddr3_init_done;
    assign dummy_o = clk_mctrl;

endmodule : bgpu_wrapper
