// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Management CPU wrapper, allows the management CPU to run at a different clock frequency
module mgmt_cpu_wrapper #(
    // Memory Address width in bits
    parameter int unsigned AddressWidth = 32,

    /// OBI Bus Types
    parameter type obi_req_t    = logic,
    parameter type obi_rsp_t    = logic,
    parameter type obi_a_chan_t = logic,
    parameter type obi_r_chan_t = logic
) (
    // Clock and reset in clk_i domain
    input logic clk_i,
    input logic rst_ni,
    input logic testmode_i,

    // Management CPU Debug Request
    input logic cpu_dbg_req_i,

    // OBI Interface in clk_i domain
    output obi_req_t cpu_imem_obi_req_o,
    input  obi_rsp_t cpu_imem_obi_rsp_i,

    output obi_req_t cpu_dmem_obi_req_o,
    input  obi_rsp_t cpu_dmem_obi_rsp_i,

    // Management CPU clock
    input logic mgmt_cpu_clk_i
);
    // #######################################################################################
    // # Typedefs                                                                            #
    // #######################################################################################

    typedef logic [31:0] addr_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Management CPU Reset and Debug Request
    logic mgmt_rst_n, mgmt_dbg_req;

    // Management CPU Address
    addr_t mgmt_boot_addr, mgmt_imem_addr, mgmt_dmem_addr;

    // Management CPU OBI Request and Response
    obi_req_t mgmt_imem_obi_req, mgmt_dmem_obi_req;
    obi_rsp_t mgmt_imem_obi_rsp, mgmt_dmem_obi_rsp;

    // #######################################################################################
    // # Synchronize Reset and Debug Request                                                 #
    // #######################################################################################

    rstgen i_rstgen (
        .clk_i      ( clk_i        ),
        .rst_ni     ( rst_ni       ),
        .test_mode_i( testmode_i   ),
        .rst_no     ( mgmt_rst_n   ),
        .init_no    ( /* Unused */ )
    );

    sync #(
        .STAGES    ( 2    ),
        .ResetValue( 1'b0 )
    ) i_sync_dbg_req (
        .clk_i   ( clk_i         ),
        .rst_ni  ( rst_ni        ),
        .serial_i( cpu_dbg_req_i ),
        .serial_o( mgmt_dbg_req  )
    );

    // #######################################################################################
    // # Boot Address                                                                        #
    // #######################################################################################

    always_comb begin : build_cpu_boot_addr
        // Boot address for the management CPU
        // We boot into the Error Subordinate
        mgmt_boot_addr = '0;
        mgmt_boot_addr[AddressWidth:0] = {1'b1, {AddressWidth{1'b0}}} + 'h5000;
    end : build_cpu_boot_addr

    // #######################################################################################
    // # Management CPU                                                                      #
    // #######################################################################################

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

        .DmHaltAddr     ( (1 << AddressWidth) + dm::HaltAddress     [31:0] ),
        .DmExceptionAddr( (1 << AddressWidth) + dm::ExceptionAddress[31:0] )
    ) i_mgmt_cpu (
        .clk_i ( mgmt_cpu_clk_i ),
        .rst_ni( mgmt_rst_n     ),

        .test_en_i( testmode_i ),
        .hart_id_i( '0         ),

        .boot_addr_i( mgmt_boot_addr ),

        .instr_req_o   ( mgmt_imem_obi_req.req     ),
        .instr_gnt_i   ( mgmt_imem_obi_rsp.gnt     ),
        .instr_rdata_i ( mgmt_imem_obi_rsp.r.rdata ),
        .instr_rvalid_i( mgmt_imem_obi_rsp.rvalid  ),
        .instr_err_i   ( mgmt_imem_obi_rsp.r.err   ),
        .instr_addr_o  ( mgmt_imem_addr            ),

        .data_req_o   ( mgmt_dmem_obi_req.req     ),
        .data_gnt_i   ( mgmt_dmem_obi_rsp.gnt     ),
        .data_wdata_o ( mgmt_dmem_obi_req.a.wdata ),
        .data_we_o    ( mgmt_dmem_obi_req.a.we    ),
        .data_be_o    ( mgmt_dmem_obi_req.a.be    ),
        .data_rvalid_i( mgmt_dmem_obi_rsp.rvalid  ),
        .data_rdata_i ( mgmt_dmem_obi_rsp.r.rdata ),
        .data_err_i   ( mgmt_dmem_obi_rsp.r.err   ),
        .data_addr_o  ( mgmt_dmem_addr            ),

        .irq_software_i( 1'b0         ),
        .irq_timer_i   ( 1'b0         ),
        .irq_external_i( 1'b0         ),
        .irq_fast_i    ( '0           ),
        .irq_nm_i      ( 1'b0         ),
        .irq_pending_o ( /* Unused */ ),

        .debug_req_i   ( mgmt_dbg_req ),
        .fetch_enable_i( 1'b1         ),
        .core_busy_o   ( /* Unused */ ),
        .crash_dump_o  ( /* Unused */ )
    );

    // Assign additional signals for CPU IMEM OBI
    assign mgmt_imem_obi_req.a.we         = 1'b0;
    assign mgmt_imem_obi_req.a.be         = '0;
    assign mgmt_imem_obi_req.a.wdata      = '0;
    assign mgmt_imem_obi_req.a.a_optional = '0;
    assign mgmt_imem_obi_req.a.aid        = '0;
    assign mgmt_imem_obi_req.a.addr       = mgmt_imem_addr[AddressWidth:0];

    // Assign additional signals for CPU DMEM OBI
    assign mgmt_dmem_obi_req.a.a_optional = '0;
    assign mgmt_dmem_obi_req.a.aid        = '0;
    assign mgmt_dmem_obi_req.a.addr       = mgmt_dmem_addr[AddressWidth:0];

    // #######################################################################################
    // # Clock Domain Crossing                                                               #
    // #######################################################################################

    cdc_fifo_gray #(
        .T( obi_a_chan_t ),

        .LOG_DEPTH  ( 2 ),
        .SYNC_STAGES( 2 )
    ) i_cdc_dmem_a (
        .src_clk_i ( mgmt_cpu_clk_i ),
        .src_rst_ni( mgmt_rst_n     ),

        .src_data_i ( mgmt_dmem_obi_req.a   ),
        .src_valid_i( mgmt_dmem_obi_req.req ),
        .src_ready_o( mgmt_dmem_obi_rsp.gnt ),

        .dst_clk_i ( clk_i  ),
        .dst_rst_ni( rst_ni ),

        .dst_data_o ( cpu_dmem_obi_req_o.a   ),
        .dst_valid_o( cpu_dmem_obi_req_o.req ),
        .dst_ready_i( cpu_dmem_obi_rsp_i.gnt )
    );

    cdc_fifo_gray #(
        .T( obi_r_chan_t ),

        .LOG_DEPTH  ( 2 ),
        .SYNC_STAGES( 2 )
    ) i_cdc_dmem_r (
        .src_clk_i ( clk_i  ),
        .src_rst_ni( rst_ni ),

        .src_data_i ( cpu_dmem_obi_rsp_i.r      ),
        .src_valid_i( cpu_dmem_obi_rsp_i.rvalid ),
        .src_ready_o( /* Unused */              ), // This might cause issues

        .dst_clk_i ( mgmt_cpu_clk_i ),
        .dst_rst_ni( mgmt_rst_n     ),

        .dst_data_o ( mgmt_dmem_obi_rsp.r      ),
        .dst_valid_o( mgmt_dmem_obi_rsp.rvalid ),
        .dst_ready_i( 1'b1                     )
    );

    cdc_fifo_gray #(
        .T( obi_a_chan_t ),

        .LOG_DEPTH  ( 2 ),
        .SYNC_STAGES( 2 )
    ) i_cdc_imem_a (
        .src_clk_i ( mgmt_cpu_clk_i ),
        .src_rst_ni( mgmt_rst_n     ),

        .src_data_i ( mgmt_imem_obi_req.a   ),
        .src_valid_i( mgmt_imem_obi_req.req ),
        .src_ready_o( mgmt_imem_obi_rsp.gnt ),

        .dst_clk_i ( clk_i  ),
        .dst_rst_ni( rst_ni ),

        .dst_data_o ( cpu_imem_obi_req_o.a   ),
        .dst_valid_o( cpu_imem_obi_req_o.req ),
        .dst_ready_i( cpu_imem_obi_rsp_i.gnt )
    );

    cdc_fifo_gray #(
        .T( obi_r_chan_t ),

        .LOG_DEPTH  ( 2 ),
        .SYNC_STAGES( 2 )
    ) i_cdc_imem_r (
        .src_clk_i ( clk_i  ),
        .src_rst_ni( rst_ni ),

        .src_data_i ( cpu_imem_obi_rsp_i.r      ),
        .src_valid_i( cpu_imem_obi_rsp_i.rvalid ),
        .src_ready_o( /* Unused */              ), // This might cause issues

        .dst_clk_i ( mgmt_cpu_clk_i ),
        .dst_rst_ni( mgmt_rst_n     ),

        .dst_data_o ( mgmt_imem_obi_rsp.r      ),
        .dst_valid_o( mgmt_imem_obi_rsp.rvalid ),
        .dst_ready_i( 1'b1                     )
    );

endmodule : mgmt_cpu_wrapper
