// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "axi/typedef.svh"
`include "obi/typedef.svh"
`include "register_interface/typedef.svh"

/// BGPU SoC top-level module
// Contains:
// - JTAG debug interface
// - Dummy Memory
module bgpu_soc #(
    // Memory Address width in bits
    parameter int unsigned AddressWidth = 32
) (
    // Clock and reset
    input logic ext_clk_i,
    input logic ext_rst_ni,

    /// JTAG interface
    input  logic jtag_tck_i,
    input  logic jtag_tdi_i,
    output logic jtag_tdo_o,
    input  logic jtag_tms_i,
    input  logic jtag_trst_ni
);
    // #######################################################################################
    // # Local Parameters                                                                    #
    // #######################################################################################

    // Width of the debug buses
    localparam int unsigned DbgWidth = 32;

    // OBI configuration for the debug interface
    localparam obi_pkg::obi_cfg_t DbgObiCfg = obi_pkg::obi_default_cfg(AddressWidth, DbgWidth,
        1, obi_pkg::ObiMinimalOptionalConfig);

    // #######################################################################################
    // # Typedefs                                                                            #
    // #######################################################################################

    typedef logic [    DbgWidth-1:0] dbg_data_t;
    typedef logic [  DbgWidth/8-1:0] dbg_be_t;
    typedef logic [AddressWidth-1:0] addr_t;

    // Debug Manager OBI, Register Interface and AXI types
    /* verilator lint_off ASCRANGE */
    `OBI_TYPEDEF_DEFAULT_ALL(dbg_obi, DbgObiCfg)
    /* verilator lint_on ASCRANGE */
    `REG_BUS_TYPEDEF_ALL(dbg_req_reg, addr_t, dbg_data_t,
        dbg_be_t)
    `AXI_TYPEDEF_ALL(dbg_axi, addr_t, logic, dbg_data_t, dbg_be_t, logic)

    // Compute Cluster Instruction Memory AXI types
    // `AXI_TYPEDEF_ALL(imem_axi, imem_axi_addr_t, imem_axi_id_t, imem_data_t, imem_data_strb_t,
    //     logic)

    // Compute Cluster Data Memory AXI types
    // `AXI_TYPEDEF_ALL(mem_axi, addr_t, mem_axi_id_t, block_data_t, block_mask_t, logic)

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Clock, reset and testmode
    logic clk, rst_n, testmode;

    // dbg req bus
    dbg_obi_req_t dbg_req_obi_req;
    dbg_obi_rsp_t dbg_req_obi_rsp;

    // DMI signals
    logic dmi_rst_n;

    logic         dmi_req_valid,  dmi_req_ready;
    dm::dmi_req_t dmi_req;

    logic          dmi_resp_valid, dmi_resp_ready;
    dm::dmi_resp_t dmi_resp;

    dbg_req_reg_req_t dbg_req_reg_req;
    dbg_req_reg_rsp_t dbg_req_reg_rsp;

    dbg_axi_req_t  dbg_axi_req;
    dbg_axi_resp_t dbg_axi_rsp;

    // #######################################################################################
    // # Clock and Reset                                                                     #
    // #######################################################################################

    assign clk   = ext_clk_i;
    assign rst_n = ext_rst_ni;

    // #######################################################################################
    // # JTAG Debug Interface                                                                #
    // #######################################################################################

    dmi_jtag #(
        .IdcodeValue( 32'h00000DB3 )
    ) i_dmi_jtag (
        .clk_i     ( clk      ),
        .rst_ni    ( rst_n    ),
        .testmode_i( testmode ),

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

    localparam dm::hartinfo_t HARTINFO = '{
        zero1: '0,
        nscratch: 2,
        zero0: '0,
        dataaccess: 1'b1,
        datasize: dm::DataCount,
        dataaddr: dm::DataAddr
    };

    dm_obi_top #(
        .BusWidth( DbgWidth ),
        .IdWidth ( 1        )
    ) i_dm_top (
        .clk_i     ( clk      ),
        .rst_ni    ( rst_n    ),
        .testmode_i( testmode ),

        .ndmreset_o   ( /* Unused */ ),
        .dmactive_o   ( /* Unused */ ),
        .debug_req_o  ( /* Unused */ ),
        .unavailable_i( 1'b0         ),
        .hartinfo_i   ( HARTINFO     ),

        .slave_req_i   ( 1'b0         ),
        .slave_we_i    ( 1'b0         ),
        .slave_addr_i  ( '0           ),
        .slave_be_i    ( '0           ),
        .slave_wdata_i ( '0           ),
        .slave_aid_i   ( '0           ),
        .slave_gnt_o   ( /* Unused */ ),
        .slave_rvalid_o( /* Unused */ ),
        .slave_rdata_o ( /* Unused */ ),
        .slave_rid_o   ( /* Unused */ ),

        .master_req_o      ( dbg_req_obi_req.req     ),
        .master_addr_o     ( dbg_req_obi_req.a.addr  ),
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

    // Assign unused signals
    assign dbg_req_obi_req.a.aid = '0;
    assign dbg_req_obi_req.a.a_optional = '0;

    // Convert OBI request to Register Interface
    periph_to_reg #(
        .AW   ( AddressWidth      ),
        .DW   ( DbgWidth          ),
        .BW   ( 8                 ),
        .IW   ( 1                 ),
        .req_t( dbg_req_reg_req_t ),
        .rsp_t( dbg_req_reg_rsp_t )
    ) i_dmi_obi_to_reg (
        .clk_i ( clk   ),
        .rst_ni( rst_n ),

        .req_i  ( dbg_req_obi_req.req     ),
        .add_i  ( dbg_req_obi_req.a.addr  ),
        .wen_i  ( ~dbg_req_obi_req.a.we   ),
        .wdata_i( dbg_req_obi_req.a.wdata ),
        .be_i   ( dbg_req_obi_req.a.be    ),
        .id_i   ( dbg_req_obi_req.a.aid   ),

        .gnt_o    ( dbg_req_obi_rsp.gnt     ),
        .r_rdata_o( dbg_req_obi_rsp.r.rdata ),
        .r_opc_o  ( dbg_req_obi_rsp.r.err   ),
        .r_id_o   ( dbg_req_obi_rsp.r.rid   ),
        .r_valid_o( dbg_req_obi_rsp.rvalid  ),

        .reg_req_o( dbg_req_reg_req ),
        .reg_rsp_i( dbg_req_reg_rsp )
    );
    assign dbg_req_obi_rsp.r.r_optional = '0;

    // Convert Register Interface to AXI
    reg_to_axi #(
        .DataWidth( DbgWidth          ),
        .reg_req_t( dbg_req_reg_req_t ),
        .reg_rsp_t( dbg_req_reg_rsp_t ),
        .axi_req_t( dbg_axi_req_t     ),
        .axi_rsp_t( dbg_axi_resp_t    )
    ) i_dmi_reg_to_axi (
        .clk_i ( clk   ),
        .rst_ni( rst_n ),

        .reg_req_i( dbg_req_reg_req ),
        .reg_rsp_o( dbg_req_reg_rsp ),

        .axi_req_o( dbg_axi_req ),
        .axi_rsp_i( dbg_axi_rsp )
    );

    // #######################################################################################
    // # Dummy Memory                                                                        #
    // #######################################################################################

    axi_sim_mem #(
        .AddrWidth        ( AddressWidth        ),
        .DataWidth        ( DbgWidth            ),
        .IdWidth          ( 1                   ),
        .UserWidth        ( 1                   ),
        .NumPorts         ( 1                   ),
        .axi_req_t        ( dbg_axi_req_t       ),
        .axi_rsp_t        ( dbg_axi_resp_t      ),
        .WarnUninitialized( 1'b1                ),
        .UninitializedData( "ones"              ),
        .ClearErrOnAccess ( 1'b0                ),
        .ApplDelay        ( 1ns                 ),
        .AcqDelay         ( 9ns                 )
    ) i_mem (
        .clk_i ( clk   ),
        .rst_ni( rst_n ),

        .axi_req_i( dbg_axi_req ),
        .axi_rsp_o( dbg_axi_rsp ),

        .mon_w_valid_o     ( /* Unused */ ),
        .mon_w_addr_o      ( /* Unused */ ),
        .mon_w_data_o      ( /* Unused */ ),
        .mon_w_id_o        ( /* Unused */ ),
        .mon_w_user_o      ( /* Unused */ ),
        .mon_w_beat_count_o( /* Unused */ ),
        .mon_w_last_o      ( /* Unused */ ),

        .mon_r_valid_o     ( /* Unused */ ),
        .mon_r_addr_o      ( /* Unused */ ),
        .mon_r_data_o      ( /* Unused */ ),
        .mon_r_id_o        ( /* Unused */ ),
        .mon_r_user_o      ( /* Unused */ ),
        .mon_r_beat_count_o( /* Unused */ ),
        .mon_r_last_o      ( /* Unused */ )
    );

endmodule : bgpu_soc
