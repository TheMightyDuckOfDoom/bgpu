// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "axi/typedef.svh"
`include "obi/typedef.svh"
`include "register_interface/typedef.svh"

/// BGPU SoC top-level module
// Contains:
// - Compute Clusters
// - JTAG debug interface
// - Dummy Memory
module bgpu_soc #(
    /// Number of Compute Clusters
    parameter int unsigned ComputeClusters = 1,
    /// Number of Compute Units per Cluster
    parameter int unsigned ComputeUnitsPerCluster = 1,
    /// Width of the Program Counter
    parameter int unsigned PcWidth = 16,
    /// Number of warps
    parameter int unsigned NumWarps = 8,
    /// Number of threads per warp
    parameter int unsigned WarpWidth = 4,
    /// Encoded instruction width
    parameter int unsigned EncInstWidth = 32,
    /// Number of inflight instructions per warp
    parameter int unsigned InflightInstrPerWarp = 4,
    /// How many registers can each warp access as operand or destination
    parameter int unsigned RegIdxWidth = 8,
    /// How many operands each instruction can have
    parameter int unsigned OperandsPerInst = 2,
    /// How many register banks are available
    parameter int unsigned NumBanks = 4,
    /// How many operand collectors are available
    parameter int unsigned NumOperandCollectors = 6,
    /// Should the register banks be dual ported?
    parameter bit          DualPortRegisterBanks = 1'b0,
    /// Width of the registers
    parameter int unsigned RegWidth = 32,
    // Memory Address width in bits
    parameter int unsigned AddressWidth = 32,
    // Memory Block index width -> Memory request width is 2^BlockIdxBits bytes
    parameter int unsigned BlockIdxBits = 4,
    // Width of the id for requests queue
    parameter int unsigned OutstandingReqIdxWidth = 3,
    // Number of cache lines in the instruction cache
    parameter int unsigned NumIClines = 8,
    // Number of bits for the instruction cache line index
    parameter int unsigned IClineIdxBits = 2,
    // How many bits are used to index thread blocks inside a thread group?
    parameter int unsigned TblockIdxBits = 8,
    // How many bits are used to identify a thread group?
    parameter int unsigned TgroupIdBits = 8
) (
    // Clock and reset
    input logic ext_clk_i,
    input logic ext_rst_ni,

    // Testmode
    input logic testmode_i,

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

    // I-Cacheline width in bits
    localparam int unsigned ImemDataWidth    = (1 << IClineIdxBits) * EncInstWidth;
    // I-Cacheline width in bytes
    localparam int unsigned ImemAxiStrbWidth = ImemDataWidth / 8;
    // Address in I-Cachelines
    localparam int unsigned ImemAddrWidth    = PcWidth - IClineIdxBits;
    // Address in bytes
    localparam int unsigned ImemAxiAddrWidth = PcWidth + $clog2(EncInstWidth / 8);
    // AXI ID width for the Compute Unit IMEM
    localparam int unsigned ImemCcAxiIdWidth = ComputeUnitsPerCluster > 1
                                                ? $clog2(ComputeUnitsPerCluster) + 1 : 1;

    // Width of the data block address -> blockwise address
    localparam int unsigned BlockAddrWidth = AddressWidth - BlockIdxBits;
    // Width of the data block in bytes
    localparam int unsigned BlockWidth     = 1 << BlockIdxBits;

    // Width of the thread idx inside a warp
    localparam int unsigned ThreadIdxWidth = WarpWidth > 1 ? $clog2(WarpWidth) : 1;

    // Width of the memory axi id for the Compute Clusters
    localparam int unsigned MemCcAxiIdWidth = $clog2(ComputeUnitsPerCluster)
                                                + OutstandingReqIdxWidth + ThreadIdxWidth;

    // Widht of the memory axi id
    localparam int unsigned MemAxiIdWidth = $clog2(ComputeClusters) + MemCcAxiIdWidth;

    // #######################################################################################
    // # Typedefs                                                                            #
    // #######################################################################################

    typedef logic [     DbgWidth-1:0] dbg_data_t;
    typedef logic [   DbgWidth/8-1:0] dbg_be_t;
    typedef logic [ AddressWidth-1:0] addr_t;
    typedef logic [      PcWidth-1:0] pc_t;
    typedef logic [TblockIdxBits-1:0] tblock_idx_t;
    typedef logic [ TgroupIdBits-1:0] tgroup_id_t;

    // Instruction Memory Types
    typedef logic [ImemAddrWidth-1:0] imem_addr_t;
    typedef logic [ImemDataWidth-1:0] imem_data_t;

    typedef logic [ImemAxiStrbWidth-1:0] imem_data_strb_t;
    typedef logic [ImemAxiAddrWidth-1:0] imem_axi_addr_t;

    typedef logic [ImemCcAxiIdWidth-1:0] imem_cc_axi_id_t;

    `AXI_TYPEDEF_ALL(cc_imem_axi, imem_axi_addr_t, imem_cc_axi_id_t, imem_data_t, imem_data_strb_t,
        logic)

    // Data Memory Types
    typedef logic [ BlockAddrWidth-1:0] block_addr_t;
    typedef logic [     BlockWidth-1:0] block_mask_t;
    typedef logic [ BlockWidth * 8-1:0] block_data_t;
    typedef logic [MemCcAxiIdWidth-1:0] mem_cc_axi_id_t;
    typedef logic [  MemAxiIdWidth-1:0] mem_axi_id_t;

    // Compute Cluster Data Memory AXI types
    `AXI_TYPEDEF_ALL(cc_mem_axi, addr_t, mem_cc_axi_id_t, block_data_t, block_mask_t, logic)

    // Data Memory AXI types
    `AXI_TYPEDEF_ALL(mem_axi, addr_t, mem_axi_id_t, block_data_t, block_mask_t, logic)

    // Debug Manager OBI, Register Interface and AXI types

    /* verilator lint_off ASCRANGE */
    `OBI_TYPEDEF_DEFAULT_ALL(dbg_obi, DbgObiCfg)
    /* verilator lint_on ASCRANGE */
    `REG_BUS_TYPEDEF_ALL(dbg_req_reg, addr_t, dbg_data_t,
        dbg_be_t)
    `AXI_TYPEDEF_ALL(dbg_axi, addr_t, logic, dbg_data_t, dbg_be_t, logic)

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

    /// Compute Cluster signals

    // Instruction Memory AXI
    cc_imem_axi_req_t  [ComputeClusters-1:0] cc_imem_axi_req;
    cc_imem_axi_resp_t [ComputeClusters-1:0] cc_imem_axi_rsp;

    // Data Memory AXI
    cc_mem_axi_req_t  [ComputeClusters-1:0] cc_mem_axi_req;
    cc_mem_axi_resp_t [ComputeClusters-1:0] cc_mem_axi_rsp;

    mem_axi_req_t  mem_axi_req;
    mem_axi_resp_t mem_axi_rsp;

    // Warp allocation
    logic warp_free, allocate_warp;

    logic [ComputeClusters-1:0] cc_allocate_warp, cc_warp_free;
    pc_t                        cc_allocate_pc;
    addr_t                      cc_allocate_dp_addr;
    tblock_idx_t                cc_allocate_tblock_idx;
    tgroup_id_t                 cc_allocate_tgroup_id;

    // Warp completion
    logic       tblock_done, tblock_done_ready;
    tgroup_id_t tblock_done_id;

    logic       [ComputeClusters-1:0] cc_done, cc_done_ready;
    tgroup_id_t [ComputeClusters-1:0] cc_done_id;

    // #######################################################################################
    // # Clock and Reset                                                                     #
    // #######################################################################################

    assign clk   = ext_clk_i;
    assign rst_n = ext_rst_ni;

    assign testmode = 1'b0;

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

`ifndef SYNTHESIS
    axi_sim_mem #(
        .AddrWidth        ( AddressWidth   ),
        .DataWidth        ( DbgWidth       ),
        .IdWidth          ( 1              ),
        .UserWidth        ( 1              ),
        .NumPorts         ( 1              ),
        .axi_req_t        ( dbg_axi_req_t  ),
        .axi_rsp_t        ( dbg_axi_resp_t ),
        .WarnUninitialized( 1'b1           ),
        .UninitializedData( "ones"         ),
        .ClearErrOnAccess ( 1'b0           ),
        .ApplDelay        ( 1ns            ),
        .AcqDelay         ( 9ns            )
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
`else
    axi_err_slv #(
        .AxiIdWidth( 1              ),
        .axi_req_t ( dbg_axi_req_t  ),
        .axi_resp_t( dbg_axi_resp_t ),
        .RespWidth ( DbgWidth       ),
        .RespData  ( 'hBADCAB1E     ),
        .ATOPs     ( 1'b0           ),
        .MaxTrans  ( 1              )
    ) i_mem (
        .clk_i ( clk      ),
        .rst_ni( rst_n    ),
        .test_i( testmode ),

        .slv_req_i ( dbg_axi_req ),
        .slv_resp_o( dbg_axi_rsp )
    );
`endif

    // #######################################################################################
    // # Compute Clusters                                                                    #
    // #######################################################################################

    // Can allocate a warp if there is atleast one free cluster
    assign warp_free = |cc_warp_free;

    // Allocate a warp in the first free cluster
    always_comb begin : select_cc_for_allocation
        cc_allocate_warp = '0;
        for(int unsigned i = 0; i < ComputeClusters; i++) begin : loop_cc
            if (cc_warp_free[i]) begin : free_cc
                cc_allocate_warp[i] = 1'b1;
                break; // Only allocate in the first free cluster
            end : free_cc
        end : loop_cc
    end : select_cc_for_allocation

    // Thread block completion
    stream_arbiter #(
        .DATA_T ( tgroup_id_t     ),
        .N_INP  ( ComputeClusters ),
        .ARBITER( "rr"            )
    ) i_tblock_done_arbiter (
        .clk_i ( clk   ),
        .rst_ni( rst_n ),

        .inp_data_i ( cc_done_id    ),
        .inp_valid_i( cc_done       ),
        .inp_ready_o( cc_done_ready ),

        .oup_data_o ( tblock_done_id    ),
        .oup_valid_o( tblock_done       ),
        .oup_ready_i( tblock_done_ready )
    );

    // Generate Compute Clusters
    for(genvar i = 0; i < ComputeClusters; i++) begin : gen_compute_clusters
        compute_cluster #(
            .ComputeUnits          ( ComputeUnitsPerCluster ),
            .PcWidth               ( PcWidth                ),
            .NumWarps              ( NumWarps               ),
            .WarpWidth             ( WarpWidth              ),
            .EncInstWidth          ( EncInstWidth           ),
            .InflightInstrPerWarp  ( InflightInstrPerWarp   ),
            .RegIdxWidth           ( RegIdxWidth            ),
            .OperandsPerInst       ( OperandsPerInst        ),
            .NumBanks              ( NumBanks               ),
            .NumOperandCollectors  ( NumOperandCollectors   ),
            .DualPortRegisterBanks ( DualPortRegisterBanks  ),
            .RegWidth              ( RegWidth               ),
            .AddressWidth          ( AddressWidth           ),
            .BlockIdxBits          ( BlockIdxBits           ),
            .OutstandingReqIdxWidth( OutstandingReqIdxWidth ),
            .NumIClines            ( NumIClines             ),
            .IClineIdxBits         ( IClineIdxBits          ),
            .TblockIdxBits         ( TblockIdxBits          ),
            .TgroupIdBits          ( TgroupIdBits           ),

            .imem_axi_req_t ( cc_imem_axi_req_t  ),
            .imem_axi_resp_t( cc_imem_axi_resp_t ),

            .mem_axi_req_t ( cc_mem_axi_req_t  ),
            .mem_axi_resp_t( cc_mem_axi_resp_t )
        ) i_cc (
            .clk_i ( clk   ),
            .rst_ni( rst_n ),

            .testmode_i( testmode_i ),

            .warp_free_o          ( cc_warp_free    [i]    ),
            .allocate_warp_i      ( cc_allocate_warp[i]    ),
            .allocate_pc_i        ( cc_allocate_pc         ),
            .allocate_dp_addr_i   ( cc_allocate_dp_addr    ),
            .allocate_tblock_idx_i( cc_allocate_tblock_idx ),
            .allocate_tgroup_id_i ( cc_allocate_tgroup_id  ),

            .tblock_done_ready_i( cc_done_ready[i] ),
            .tblock_done_o      ( cc_done      [i] ),
            .tblock_done_id_o   ( cc_done_id   [i] ),

            .imem_req_o( cc_imem_axi_req[i] ),
            .imem_rsp_i( cc_imem_axi_rsp[i] ),

            .mem_req_o( cc_mem_axi_req[i] ),
            .mem_rsp_i( cc_mem_axi_rsp[i] )
        );
    end : gen_compute_clusters

    // #######################################################################################
    // # Compute Cluster Mem Interconnect                                                    #
    // #######################################################################################

    axi_mux #(
        .SlvAxiIDWidth( MemCcAxiIdWidth      ),
        .slv_aw_chan_t( cc_mem_axi_aw_chan_t ),
        .mst_aw_chan_t( mem_axi_aw_chan_t    ),
        .w_chan_t     ( cc_mem_axi_w_chan_t  ),
        .slv_b_chan_t ( cc_mem_axi_b_chan_t  ),
        .mst_b_chan_t ( mem_axi_b_chan_t     ),
        .slv_ar_chan_t( cc_mem_axi_ar_chan_t ),
        .mst_ar_chan_t( mem_axi_ar_chan_t    ),
        .slv_r_chan_t ( cc_mem_axi_r_chan_t  ),
        .mst_r_chan_t ( mem_axi_r_chan_t     ),
        .slv_req_t    ( cc_mem_axi_req_t     ),
        .slv_resp_t   ( cc_mem_axi_resp_t    ),
        .mst_req_t    ( mem_axi_req_t        ),
        .mst_resp_t   ( mem_axi_resp_t       ),
        .NoSlvPorts   ( ComputeClusters      ),
        .MaxWTrans    ( ComputeClusters      ), // This might need adjustment
        .FallThrough  ( 1'b0                 ),
        .SpillAw      ( 1'b1                 ),
        .SpillW       ( 1'b1                 ),
        .SpillB       ( 1'b1                 ),
        .SpillAr      ( 1'b1                 ),
        .SpillR       ( 1'b1                 )
    ) i_mem_mux (
        .clk_i ( clk      ),
        .rst_ni( rst_n    ),
        .test_i( testmode ),

        .slv_reqs_i ( cc_mem_axi_req ),
        .slv_resps_o( cc_mem_axi_rsp ),

        .mst_req_o ( mem_axi_req ),
        .mst_resp_i( mem_axi_rsp )
    );

endmodule : bgpu_soc
