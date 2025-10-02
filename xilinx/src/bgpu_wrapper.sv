// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// BGPU Wrapper for Xilinx FPGAs
// Contains:
// - BGPU SoC
// - DDR3 Memory Controller
module bgpu_wrapper (
    /// System Clock and Reset
    input logic sys_clk_200_pi, // Differential 200MHz Clock
    input logic sys_clk_200_ni, // Differential 200MHz Clock

    input logic sys_clk_100_i, // 100MHz Clock

    input logic sys_rst_ni, // System Reset

    /// DDR3 Memory Interface
    output logic [13:0] ddr3_addr,
    output logic [ 2:0] ddr3_ba,
    output logic        ddr3_cas_n,
    output logic [ 0:0] ddr3_ck_n,
    output logic [ 0:0] ddr3_ck_p,
    output logic        ddr3_cke,
    output logic        ddr3_ras_n,
    output logic        ddr3_reset_n,
    output logic        ddr3_we_n,
    inout  logic [63:0] ddr3_dq,
    inout  logic [ 7:0] ddr3_dqs_n,
    inout  logic [ 7:0] ddr3_dqs_p,
    output logic [ 0:0] ddr3_cs_n,
    output logic [ 7:0] ddr3_dm,
    output logic [ 0:0] ddr3_odt,

    /// Status LEDs
    output logic [7:0] led_o
);
    // #######################################################################################
    // # Local Parameters                                                                    #
    // #######################################################################################

    // Should BGPU use the DDR3 Memory Controller?
    localparam bit UseMctrl = 1'b1;

    localparam int unsigned WarpWidth              = 4;
    localparam int unsigned ComputeUnitsPerCluster = 4;
    localparam int unsigned OutstandingReqIdxWidth = 1;
    localparam int unsigned ComputeClusters        = 1;
    
    // 1GB DDR3 Sodimm
    localparam int unsigned MctrlAddressWidth = 30;  // 1GB DDR3
    localparam int unsigned MctrlWidth        = 512; // 64 bytes DDR3 Burst

    // Width of the thread idx inside a warp
    localparam int unsigned ThreadIdxWidth = WarpWidth > 1 ? $clog2(WarpWidth) : 1;

    // Width of the memory axi id for the Compute Clusters
    localparam int unsigned MemCcAxiIdWidth = $clog2(ComputeUnitsPerCluster)
                                                + OutstandingReqIdxWidth + ThreadIdxWidth;

    // Width of the memory axi id
    localparam int unsigned MemAxiIdWidth = $clog2(ComputeClusters) + MemCcAxiIdWidth;

    // With of the Memory Controller AXI ID
    localparam int unsigned MctrlAxiIdWidth = MemAxiIdWidth + 2;

    // #######################################################################################
    // # Type Definitions                                                                    #
    // #######################################################################################

    // Memory Controller AXI Interface Types
    typedef logic [MctrlAddressWidth-1:0] mctrl_addr_t;
    typedef logic [       MctrlWidth-1:0] mctrl_data_t;
    typedef logic [     MctrlWidth/8-1:0] mctrl_strb_t;
    typedef logic [  MctrlAxiIdWidth-1:0] mctrl_axi_id_t;

    // Memory Controller AXI Interface
    `AXI_TYPEDEF_ALL(mctrl_axi, mctrl_addr_t, mctrl_axi_id_t, mctrl_data_t, mctrl_strb_t, logic)

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // SoC Reset
    logic soc_rst_n;

    // Clocks
    logic sys_clk_200, sys_clk_200_unbuffered;
    logic sys_clk_100, sys_clk_100_unbuffered;
    
    /// Memory Controller Signals
    // Calibration Complete
    logic mctrl_init_calib_complete;

    // Clock and Reset
    logic mctrl_axi_clk, mctrl_rst;

    // AXI Interface
    mctrl_axi_req_t  mctrl_axi_req;
    mctrl_axi_resp_t mctrl_axi_rsp;

    // #######################################################################################
    // # Clock                                                                               #
    // #######################################################################################

    IBUFGDS #(
        .DIFF_TERM( "TRUE" )
    ) i_sys_clk_200_diff_ibuf (
        .I ( sys_clk_200_pi         ),
        .IB( sys_clk_200_ni         ),
        .O ( sys_clk_200_unbuffered )
    );

    BUFG i_sys_clk_200_buf (
        .I( sys_clk_200_unbuffered ),
        .O( sys_clk_200            )
    );

    IBUFG i_sys_clk_100_ibuf (
        .I ( sys_clk_100_i          ),
        .O ( sys_clk_100_unbuffered )
    );

    BUFG i_sys_clk_100_buf (
        .I( sys_clk_100_unbuffered ),
        .O( sys_clk_100            )
    );

    // #######################################################################################
    // # Reset                                                                               #
    // #######################################################################################

    assign soc_rst_n = (!mctrl_rst) & mctrl_init_calib_complete;

    // #######################################################################################
    // # BGPU SoC                                                                            #
    // #######################################################################################

    bgpu_soc #(
        .MctrlWidth       ( MctrlWidth        ),
        .MctrlAddressWidth( MctrlAddressWidth ),

        .WarpWidth             ( WarpWidth              ),
        .ComputeUnitsPerCluster( ComputeUnitsPerCluster ),
        .OutstandingReqIdxWidth( OutstandingReqIdxWidth ),
        .ComputeClusters       ( ComputeClusters        ),

        .ExtMctrl           ( UseMctrl         ),
        .ext_mctrl_axi_req_t( mctrl_axi_req_t  ),
        .ext_mctrl_axi_rsp_t( mctrl_axi_resp_t )
    ) i_bgpu (
        .clk_i ( mctrl_axi_clk ),
        .rst_ni( soc_rst_n     ),

        .testmode_i( 1'b0 ),

        .mgmt_cpu_clk_i( sys_clk_100 ),

        // Using BSCANE2 internally
        .jtag_tck_i  ( 1'b0           ),
        .jtag_tdi_i  ( 1'b0           ),
        .jtag_tms_i  ( 1'b0           ),
        .jtag_trst_ni( 1'b1           ),
        .jtag_tdo_o  ( /* Not Used */ ),

        .mctrl_axi_req_o( mctrl_axi_req ),
        .mctrl_axi_rsp_i( mctrl_axi_rsp )
    );

    // #######################################################################################
    // # Status LEDs                                                                         #
    // #######################################################################################

    // LEDs are active low
    assign led_o[0] = !mctrl_init_calib_complete; // Lit when memory controller is ready
    assign led_o[1] = !soc_rst_n; // Lit when not in reset
    assign led_o[2] = sys_rst_ni; // Lit when reset button is pressed

    assign led_o[7:3] = '1; // Unused

    // #######################################################################################
    // # DDR3 Memory Controller                                                              #
    // #######################################################################################

    memory_controller i_ddr3_mctrl (
        // Memory interface ports
        .ddr3_addr   ( ddr3_addr    ),
        .ddr3_ba     ( ddr3_ba      ),
        .ddr3_cas_n  ( ddr3_cas_n   ),
        .ddr3_ck_n   ( ddr3_ck_n    ),
        .ddr3_ck_p   ( ddr3_ck_p    ),
        .ddr3_cke    ( ddr3_cke     ),
        .ddr3_ras_n  ( ddr3_ras_n   ),
        .ddr3_reset_n( ddr3_reset_n ),
        .ddr3_we_n   ( ddr3_we_n    ),
        .ddr3_dq     ( ddr3_dq      ),
        .ddr3_dqs_n  ( ddr3_dqs_n   ),
        .ddr3_dqs_p  ( ddr3_dqs_p   ),
	    .ddr3_cs_n   ( ddr3_cs_n    ),
        .ddr3_dm     ( ddr3_dm      ),
        .ddr3_odt    ( ddr3_odt     ),

        .init_calib_complete( mctrl_init_calib_complete ),
      
        // Application interface ports
        .ui_clk         ( mctrl_axi_clk  ),
        .ui_clk_sync_rst( mctrl_rst      ),
        .mmcm_locked    ( /* Not Used */ ),
        
        .app_sr_req   ( 1'b0           ),
        .app_ref_req  ( 1'b0           ),
        .app_zq_req   ( 1'b0           ),
        .app_sr_active( /* Not Used */ ),
        .app_ref_ack  ( /* Not Used */ ),
        .app_zq_ack   ( /* Not Used */ ),

        // AXI4 Reset
        .aresetn( soc_rst_n ),

        .s_axi_awid   ( mctrl_axi_req.aw.id    ),
        .s_axi_awaddr ( mctrl_axi_req.aw.addr  ),
        .s_axi_awlen  ( mctrl_axi_req.aw.len   ),
        .s_axi_awsize ( mctrl_axi_req.aw.size  ),
        .s_axi_awburst( mctrl_axi_req.aw.burst ),
        .s_axi_awlock ( mctrl_axi_req.aw.lock  ),
        .s_axi_awcache( mctrl_axi_req.aw.cache ),
        .s_axi_awprot ( mctrl_axi_req.aw.prot  ),
        .s_axi_awqos  ( mctrl_axi_req.aw.qos   ),
        .s_axi_awvalid( mctrl_axi_req.aw_valid ),
        .s_axi_awready( mctrl_axi_rsp.aw_ready ),

        .s_axi_wdata ( mctrl_axi_req.w.data   ),
        .s_axi_wstrb ( mctrl_axi_req.w.strb   ),
        .s_axi_wlast ( mctrl_axi_req.w.last   ),
        .s_axi_wvalid( mctrl_axi_req.w_valid  ),
        .s_axi_wready( mctrl_axi_rsp.w_ready  ),

        .s_axi_bready( mctrl_axi_req.b_ready  ),
        .s_axi_bid   ( mctrl_axi_rsp.b.id     ),
        .s_axi_bresp ( mctrl_axi_rsp.b.resp   ),
        .s_axi_bvalid( mctrl_axi_rsp.b_valid  ),

        .s_axi_arid   ( mctrl_axi_req.ar.id    ),
        .s_axi_araddr ( mctrl_axi_req.ar.addr  ),
        .s_axi_arlen  ( mctrl_axi_req.ar.len   ),
        .s_axi_arsize ( mctrl_axi_req.ar.size  ),
        .s_axi_arburst( mctrl_axi_req.ar.burst ),
        .s_axi_arlock ( mctrl_axi_req.ar.lock  ),
        .s_axi_arcache( mctrl_axi_req.ar.cache ),
        .s_axi_arprot ( mctrl_axi_req.ar.prot  ),
        .s_axi_arqos  ( mctrl_axi_req.ar.qos   ),
        .s_axi_arvalid( mctrl_axi_req.ar_valid ),
        .s_axi_arready( mctrl_axi_rsp.ar_ready ),

        .s_axi_rready( mctrl_axi_req.r_ready  ),
        .s_axi_rid   ( mctrl_axi_rsp.r.id     ),
        .s_axi_rdata ( mctrl_axi_rsp.r.data   ),
        .s_axi_rresp ( mctrl_axi_rsp.r.resp   ),
        .s_axi_rlast ( mctrl_axi_rsp.r.last   ),
        .s_axi_rvalid( mctrl_axi_rsp.r_valid  ),

        // System Clock Ports
        .sys_clk_i( sys_clk_200 ),
        .sys_rst  ( sys_rst_ni  ),

        // Device Temperature
        .device_temp( /* Not Used */ )
    ); 

endmodule : bgpu_wrapper
