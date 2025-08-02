// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "obi/typedef.svh"
`include "register_interface/typedef.svh"

/// Control domain for the BGPU SoC
// Contains:
// - Clock and Reset Management
// - JTAG Debug Module
// - Management CPU
// - Thread Engine
// - OBI Crossbar
module control_domain #(
    /// Width of the Control Domain Bus
    parameter int CtrlWidth = 32,
    /// Width of the AXI ID
    parameter int AxiIdWidth = 1,
    /// Width of the Program Counter
    parameter int unsigned PcWidth = 16,
    // Memory Address width in bits
    parameter int unsigned AddressWidth = 32,
    // How many bits are used to index thread blocks inside a thread group?
    parameter int unsigned TblockIdxBits = 8,
    // How many bits are used to identify a thread group?
    parameter int unsigned TgroupIdBits = 8,

    /// AXI Interface
    parameter type axi_req_t  = logic,
    parameter type axi_resp_t = logic,

    /// Dependent parameter, do **not** overwrite.
    parameter type tblock_idx_t = logic [TblockIdxBits-1:0],
    parameter type tgroup_id_t  = logic [ TgroupIdBits-1:0],
    parameter type addr_t       = logic [ AddressWidth-1:0],
    parameter type pc_t         = logic [      PcWidth-1:0]
)(
    // Clock and reset
    input  logic clk_i,
    output logic clk_o,
    input  logic rst_ni,
    output logic rst_no,

    // Testmode
    input logic testmode_i,

    /// JTAG interface
    input  logic jtag_tck_i,
    input  logic jtag_tdi_i,
    output logic jtag_tdo_o,
    input  logic jtag_tms_i,
    input  logic jtag_trst_ni,

    // Interface to start a new thread block -> to compute clusters
    input  logic        warp_free_i, // The is atleas one free warp that can start a new block
    output logic        allocate_warp_o,
    output pc_t         allocate_pc_o,
    output addr_t       allocate_dp_addr_o, // Data / Parameter address
    output tblock_idx_t allocate_tblock_idx_o, // Block index -> used to calculate the thread id
    output tgroup_id_t  allocate_tgroup_id_o, // Block id -> unique identifier for the block

    // Thread block completion
    output logic       tblock_done_ready_o,
    input  logic       tblock_done_i,
    input  tgroup_id_t tblock_done_id_i,

    /// AXI Interface to BGPU Domain
    output axi_req_t  axi_req_o,
    input  axi_resp_t axi_rsp_i
);
    // #######################################################################################
    // # Local Parameters                                                                    #
    // #######################################################################################

    // Upstream of the OBI Crossbar -> to Crossbar
    localparam obi_pkg::obi_cfg_t XUpsObiCfg = obi_pkg::obi_default_cfg(AddressWidth + 1, CtrlWidth,
        1, obi_pkg::ObiMinimalOptionalConfig);

    // Downstream of the OBI Crossbar -> from Crossbar
    localparam obi_pkg::obi_cfg_t XDwnObiCfg = obi_pkg::obi_default_cfg(AddressWidth + 1, CtrlWidth,
        3, obi_pkg::ObiMinimalOptionalConfig);

    // Number of address rules for the OBI Crossbar
    localparam int unsigned NumAddrRules = 3;

    // #######################################################################################
    // # Typedefs                                                                            #
    // #######################################################################################

    typedef logic [  CtrlWidth-1:0] data_t;
    typedef logic [CtrlWidth/8-1:0] be_t;

    // OBI
    `OBI_TYPEDEF_DEFAULT_ALL(xups_obi, XUpsObiCfg)
    `OBI_TYPEDEF_DEFAULT_ALL(xdwn_obi, XDwnObiCfg)

    // Register Interface -> to BGPU Domain
    `REG_BUS_TYPEDEF_ALL(reg, addr_t, data_t, be_t)

    // Address Map
    typedef struct packed {
      logic [31:0] idx;
      logic [AddressWidth:0] start_addr;
      logic [AddressWidth:0] end_addr;
    } addr_map_rule_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // DMI signals
    logic dmi_rst_n, cpu_dbg_req;

    logic [CtrlWidth-1:0] dm_master_addr, dm_slave_addr;

    logic         dmi_req_valid,  dmi_req_ready;
    dm::dmi_req_t dmi_req;

    logic          dmi_resp_valid, dmi_resp_ready;
    dm::dmi_resp_t dmi_resp;

    // OBI signals
    xups_obi_req_t dbg_req_obi_req;
    xups_obi_rsp_t dbg_req_obi_rsp;

    xups_obi_req_t cpu_imem_obi_req, cpu_imem_obi_req_cut, cpu_dmem_obi_req, cpu_dmem_obi_req_cut;
    xups_obi_rsp_t cpu_imem_obi_rsp, cpu_imem_obi_rsp_cut, cpu_dmem_obi_rsp, cpu_dmem_obi_rsp_cut;

    xdwn_obi_req_t dbg_rsp_obi_req, thread_engine_obi_req, bgpu_obi_req, err_obi_req;
    xdwn_obi_rsp_t dbg_rsp_obi_rsp, thread_engine_obi_rsp, bgpu_obi_rsp, err_obi_rsp;

    // Register Interface signals
    reg_req_t bgpu_reg_req;
    reg_rsp_t bgpu_reg_rsp;

    // Address Map
    addr_map_rule_t [NumAddrRules-1:0] ObiAddrMap;

    // Management CPU signals
    logic [CtrlWidth-1:0] cpu_imem_addr, cpu_dmem_addr, cpu_boot_addr;

    // #######################################################################################
    // # Clock and Reset                                                                     #
    // #######################################################################################

    assign clk_o  = clk_i;
    assign rst_no = rst_ni;

    // #######################################################################################
    // # JTAG Debug Interface                                                                #
    // #######################################################################################

    // JTAG TAP
    dmi_jtag #(
        .IdcodeValue( 32'h00000DB3 )
    ) i_dmi_jtag (
        .clk_i     ( clk_o      ),
        .rst_ni    ( rst_no     ),
        .testmode_i( testmode_i ),

        .dmi_rst_no     ( dmi_rst_n      ),
        .dmi_req_o      ( dmi_req        ),
        .dmi_req_valid_o( dmi_req_valid  ),
        .dmi_req_ready_i( dmi_req_ready  ),

        .dmi_resp_i      ( dmi_resp       ),
        .dmi_resp_ready_o( dmi_resp_ready ),
        .dmi_resp_valid_i( dmi_resp_valid ),

        .tck_i   ( jtag_tck_i   ),
        .tms_i   ( jtag_tms_i   ),
        .trst_ni ( jtag_trst_ni ),
        .td_i    ( jtag_tdi_i   ),
        .td_o    ( jtag_tdo_o   ),
        .tdo_oe_o( /* Unused */ )
    );

    // Hart Info
    dm::hartinfo_t hartinfo = '{
        zero1:      '0,
        nscratch:   2,
        zero0:      '0,
        dataaccess: 1'b1,
        datasize:   dm::DataCount,
        dataaddr:   dm::DataAddr
    };

    // Debug Module
    dm_obi_top #(
        .BusWidth( CtrlWidth          ),
        .IdWidth ( XDwnObiCfg.IdWidth )
    ) i_dm_top (
        .clk_i     ( clk_o      ),
        .rst_ni    ( rst_no     ),
        .testmode_i( testmode_i ),

        .ndmreset_o   ( /* Unused */ ),
        .dmactive_o   ( /* Unused */ ),
        .debug_req_o  ( cpu_dbg_req  ),
        .unavailable_i( 1'b0         ),
        .hartinfo_i   ( hartinfo     ),

        // From Crossbar
        .slave_req_i   ( dbg_rsp_obi_req.req     ),
        .slave_we_i    ( dbg_rsp_obi_req.a.we    ),
        .slave_addr_i  ( dm_slave_addr           ),
        .slave_be_i    ( dbg_rsp_obi_req.a.be    ),
        .slave_wdata_i ( dbg_rsp_obi_req.a.wdata ),
        .slave_aid_i   ( dbg_rsp_obi_req.a.aid   ),
        .slave_gnt_o   ( dbg_rsp_obi_rsp.gnt     ),
        .slave_rvalid_o( dbg_rsp_obi_rsp.rvalid  ),
        .slave_rdata_o ( dbg_rsp_obi_rsp.r.rdata ),
        .slave_rid_o   ( dbg_rsp_obi_rsp.r.rid   ),

        // To Crossbar
        .master_req_o      ( dbg_req_obi_req.req     ),
        .master_addr_o     ( dm_master_addr          ),
        .master_we_o       ( dbg_req_obi_req.a.we    ),
        .master_wdata_o    ( dbg_req_obi_req.a.wdata ),
        .master_be_o       ( dbg_req_obi_req.a.be    ),
        .master_gnt_i      ( dbg_req_obi_rsp.gnt     ),
        .master_rvalid_i   ( dbg_req_obi_rsp.rvalid  ),
        .master_rdata_i    ( dbg_req_obi_rsp.r.rdata ),
        .master_err_i      ( dbg_req_obi_rsp.r.err   ),
        .master_other_err_i( 1'b0                    ),

        .dmi_rst_ni     ( dmi_rst_n     ),
        .dmi_req_valid_i( dmi_req_valid ),
        .dmi_req_ready_o( dmi_req_ready ),
        .dmi_req_i      ( dmi_req       ),

        .dmi_resp_valid_o( dmi_resp_valid ),
        .dmi_resp_ready_i( dmi_resp_ready ),
        .dmi_resp_o      ( dmi_resp       )
    );

    // Assign additional signals
    assign dbg_req_obi_req.a.addr       = dm_master_addr[AddressWidth:0];
    assign dbg_req_obi_req.a.aid        = '0;
    assign dbg_req_obi_req.a.a_optional = '0;

    always_comb begin : build_dm_slave_addr
        dm_slave_addr = '0;
        dm_slave_addr[AddressWidth-1:0] = dbg_rsp_obi_req.a.addr[AddressWidth-1:0];
    end : build_dm_slave_addr

    // #######################################################################################
    // # Thread Engine                                                                       #
    // #######################################################################################

    obi_thread_engine #(
        .PcWidth      ( PcWidth        ),
        .AddressWidth ( AddressWidth   ),
        .TblockIdxBits( TblockIdxBits  ),
        .TgroupIdBits ( TgroupIdBits   ),
        .ObiCfg       ( XDwnObiCfg     ),
        .obi_req_t    ( xdwn_obi_req_t ),
        .obi_rsp_t    ( xdwn_obi_rsp_t )
    ) i_thread_engine (
        .clk_i ( clk_o  ),
        .rst_ni( rst_no ),

        .obi_req_i( thread_engine_obi_req ),
        .obi_rsp_o( thread_engine_obi_rsp ),

        .warp_free_i          ( warp_free_i           ),
        .allocate_warp_o      ( allocate_warp_o       ),
        .allocate_pc_o        ( allocate_pc_o         ),
        .allocate_dp_addr_o   ( allocate_dp_addr_o    ),
        .allocate_tblock_idx_o( allocate_tblock_idx_o ),
        .allocate_tgroup_id_o ( allocate_tgroup_id_o  ),

        .tblock_done_ready_o( tblock_done_ready_o ),
        .tblock_done_i      ( tblock_done_i       ),
        .tblock_done_id_i   ( tblock_done_id_i    )
    );

    // #######################################################################################
    // # Management CPU                                                                       #
    // #######################################################################################

    always_comb begin : build_cpu_boot_addr
        // Boot address for the management CPU
        // We boot into the Error Subordinate
        cpu_boot_addr = '0;
        cpu_boot_addr[AddressWidth:0] = {1'b1, {AddressWidth{1'b0}}} + 'h5000;
    end : build_cpu_boot_addr

    cve2_core #(
        .PMPEnable       ( 1'b0                ),
        .PMPGranularity  ( 0                   ),
        .PMPNumRegions   ( 1                   ),
        .MHPMCounterNum  ( 0                   ),
        .MHPMCounterWidth( 40                  ),
        .RV32E           ( 1'b1                ),
        .RV32M           ( cve2_pkg::RV32MNone ),
        .RV32B           ( cve2_pkg::RV32BNone ),
        .DbgTriggerEn    ( 1'b1                ),
        .DbgHwBreakNum   ( 1                   ),

        .DmHaltAddr      ( (1 << AddressWidth) + dm::HaltAddress     [31:0] ),
        .DmExceptionAddr ( (1 << AddressWidth) + dm::ExceptionAddress[31:0] )
    ) i_mgmt_cpu (
        .clk_i ( clk_o  ),
        .rst_ni( rst_no ),

        .test_en_i( testmode_i ),
        .hart_id_i( '0         ),

        .boot_addr_i( cpu_boot_addr ),

        .instr_req_o   ( cpu_imem_obi_req.req     ),
        .instr_gnt_i   ( cpu_imem_obi_rsp.gnt     ),
        .instr_rdata_i ( cpu_imem_obi_rsp.r.rdata ),
        .instr_rvalid_i( cpu_imem_obi_rsp.rvalid  ),
        .instr_err_i   ( cpu_imem_obi_rsp.r.err   ),
        .instr_addr_o  ( cpu_imem_addr            ),

        .data_req_o   ( cpu_dmem_obi_req.req     ),
        .data_gnt_i   ( cpu_dmem_obi_rsp.gnt     ),
        .data_wdata_o ( cpu_dmem_obi_req.a.wdata ),
        .data_we_o    ( cpu_dmem_obi_req.a.we    ),
        .data_be_o    ( cpu_dmem_obi_req.a.be    ),
        .data_rvalid_i( cpu_dmem_obi_rsp.rvalid  ),
        .data_rdata_i ( cpu_dmem_obi_rsp.r.rdata ),
        .data_err_i   ( cpu_dmem_obi_rsp.r.err   ),
        .data_addr_o  ( cpu_dmem_addr            ),

        .irq_software_i( 1'b0         ),
        .irq_timer_i   ( 1'b0         ),
        .irq_external_i( 1'b0         ),
        .irq_fast_i    ( '0           ),
        .irq_nm_i      ( 1'b0         ),
        .irq_pending_o ( /* Unused */ ),

        .debug_req_i   ( cpu_dbg_req  ),
        .fetch_enable_i( 1'b1         ),
        .core_busy_o   ( /* Unused */ ),
        .crash_dump_o  ( /* Unused */ )
    );

    assign cpu_imem_obi_req.a.addr = cpu_imem_addr[AddressWidth:0];
    assign cpu_dmem_obi_req.a.addr = cpu_dmem_addr[AddressWidth:0];

    // OBI Cut for CPU IMEM and DMEM
    obi_cut #(
        .ObiCfg      ( XUpsObiCfg        ),
        .obi_a_chan_t( xups_obi_a_chan_t ),
        .obi_r_chan_t( xups_obi_r_chan_t ),
        .obi_req_t   ( xups_obi_req_t    ),
        .obi_rsp_t   ( xups_obi_rsp_t    ),
        .Bypass      ( 1'b0              ),
        .BypassReq   ( 1'b0              ),
        .BypassRsp   ( 1'b0              )
    ) i_mgmt_cpu_imem_cut (
        .clk_i ( clk_o  ),
        .rst_ni( rst_no ),

        .sbr_port_req_i( cpu_imem_obi_req ),
        .sbr_port_rsp_o( cpu_imem_obi_rsp ),

        .mgr_port_req_o( cpu_imem_obi_req_cut ),
        .mgr_port_rsp_i( cpu_imem_obi_rsp_cut )
    );

    obi_cut #(
        .ObiCfg      ( XUpsObiCfg        ),
        .obi_a_chan_t( xups_obi_a_chan_t ),
        .obi_r_chan_t( xups_obi_r_chan_t ),
        .obi_req_t   ( xups_obi_req_t    ),
        .obi_rsp_t   ( xups_obi_rsp_t    ),
        .Bypass      ( 1'b0              ),
        .BypassReq   ( 1'b0              ),
        .BypassRsp   ( 1'b0              )
    ) i_mgmt_cpu_dmem_cut (
        .clk_i ( clk_o  ),
        .rst_ni( rst_no ),

        .sbr_port_req_i( cpu_dmem_obi_req ),
        .sbr_port_rsp_o( cpu_dmem_obi_rsp ),

        .mgr_port_req_o( cpu_dmem_obi_req_cut ),
        .mgr_port_rsp_i( cpu_dmem_obi_rsp_cut )
    );

    // #######################################################################################
    // # OBI Crossbar                                                                        #
    // #######################################################################################

    /// Build Address Map

    // BGPU Domain
    assign ObiAddrMap[0] = '{ idx: 1, start_addr: '0, end_addr: {1'b0, {AddressWidth{1'b1}}} };

    // Thread Engine
    assign ObiAddrMap[1] = '{ idx: 2, start_addr: {1'b1, {AddressWidth{1'b1}}} - 'h100,
        end_addr: {1'b1, {AddressWidth{1'b1}}}};

    // Debug Interface
    assign ObiAddrMap[2] = '{ idx: 3, start_addr: {1'b1, {AddressWidth{1'b0}}},
        end_addr: {1'b1, {AddressWidth{1'b0}}} + 'h4000 };

    // Crossbar
    obi_xbar #(
        .SbrPortObiCfg     ( XUpsObiCfg        ),
        .MgrPortObiCfg     ( XDwnObiCfg        ),
        .sbr_port_obi_req_t( xups_obi_req_t    ),
        .sbr_port_a_chan_t ( xups_obi_a_chan_t ),
        .sbr_port_obi_rsp_t( xups_obi_rsp_t    ),
        .sbr_port_r_chan_t ( xups_obi_r_chan_t ),
        .mgr_port_obi_req_t( xdwn_obi_req_t    ),
        .mgr_port_obi_rsp_t( xdwn_obi_rsp_t    ),
        .NumSbrPorts       ( 3                 ),
        .NumMgrPorts       ( NumAddrRules + 1  ),
        .NumAddrRules      ( NumAddrRules      ),
        .addr_map_rule_t   ( addr_map_rule_t   ),
        .UseIdForRouting   ( 1'b1              )
    ) i_obi_xbar (
        .clk_i ( clk_o  ),
        .rst_ni( rst_no ),

        .testmode_i( testmode_i ),

        .sbr_ports_req_i( { dbg_req_obi_req, cpu_imem_obi_req_cut, cpu_dmem_obi_req_cut } ),
        .sbr_ports_rsp_o( { dbg_req_obi_rsp, cpu_imem_obi_rsp_cut, cpu_dmem_obi_rsp_cut } ),

        .mgr_ports_req_o( { dbg_rsp_obi_req, thread_engine_obi_req, bgpu_obi_req, err_obi_req } ),
        .mgr_ports_rsp_i( { dbg_rsp_obi_rsp, thread_engine_obi_rsp, bgpu_obi_rsp, err_obi_rsp } ),

        .addr_map_i( ObiAddrMap ),

        .en_default_idx_i( '1 ),
        .default_idx_i   ( '0 )
    );

    // Error Subordinate
    obi_err_sbr #(
        .ObiCfg     ( XDwnObiCfg     ),
        .obi_req_t  ( xdwn_obi_req_t ),
        .obi_rsp_t  ( xdwn_obi_rsp_t ),
        .NumMaxTrans( 1              ),
        .RspData    ( 'hBADCAB1E     )
    ) i_err_sbr (
        .clk_i     ( clk_o      ),
        .rst_ni    ( rst_no     ),
        .testmode_i( testmode_i ),

        .obi_req_i( err_obi_req ),
        .obi_rsp_o( err_obi_rsp )
    );

    // #######################################################################################
    // # OBI2AXI Converter to access BGPU Domain                                             #
    // #######################################################################################

    // Convert OBI request to Register Interface
    periph_to_reg #(
        .AW   ( AddressWidth ),
        .DW   ( CtrlWidth    ),
        .BW   ( 8            ),
        .IW   ( AxiIdWidth   ),
        .req_t( reg_req_t    ),
        .rsp_t( reg_rsp_t    )
    ) i_obi_to_reg (
        .clk_i ( clk_o  ),
        .rst_ni( rst_no ),

        .req_i  ( bgpu_obi_req.req     ),
        .add_i  ( bgpu_obi_req.a.addr[AddressWidth-1:0] ),
        .wen_i  ( ~bgpu_obi_req.a.we   ),
        .wdata_i( bgpu_obi_req.a.wdata ),
        .be_i   ( bgpu_obi_req.a.be    ),
        .id_i   ( bgpu_obi_req.a.aid   ),

        .gnt_o    ( bgpu_obi_rsp.gnt     ),
        .r_rdata_o( bgpu_obi_rsp.r.rdata ),
        .r_opc_o  ( bgpu_obi_rsp.r.err   ),
        .r_id_o   ( bgpu_obi_rsp.r.rid   ),
        .r_valid_o( bgpu_obi_rsp.rvalid  ),

        .reg_req_o( bgpu_reg_req ),
        .reg_rsp_i( bgpu_reg_rsp )
    );
    assign bgpu_obi_rsp.r.r_optional = '0;

    // Convert Register Interface to AXI
    reg_to_axi #(
        .DataWidth( CtrlWidth   ),
        .reg_req_t( reg_req_t   ),
        .reg_rsp_t( reg_rsp_t   ),
        .axi_req_t( axi_req_t   ),
        .axi_rsp_t( axi_resp_t  )
    ) i_reg_to_axi (
        .clk_i ( clk_o  ),
        .rst_ni( rst_no ),

        .reg_req_i( bgpu_reg_req ),
        .reg_rsp_o( bgpu_reg_rsp ),

        .axi_req_o( axi_req_o ),
        .axi_rsp_i( axi_rsp_i )
    );

    // #######################################################################################
    // # Assertions                                                                          #
    // #######################################################################################

`ifndef SYNTHESIS
    // Currently only 32-bit control domain is supported
    initial assert(CtrlWidth == 32)
        else $error("CtrlWidth must be 32 bits");

    // We use MSB to identify peripherals
    initial assert(AddressWidth < CtrlWidth)
        else $error("AddressWidth must be smaller than CtrlWidth");
`endif
endmodule : control_domain
