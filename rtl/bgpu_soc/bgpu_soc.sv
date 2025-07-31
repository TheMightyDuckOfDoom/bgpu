// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "axi/typedef.svh"
`include "obi/typedef.svh"
`include "register_interface/typedef.svh"

`include "common_cells/registers.svh"

/// BGPU SoC top-level module
// Contains:
// - Compute Clusters
// - JTAG debug interface
// - Dummy Memory
module bgpu_soc #(
    /// Width of the data bus to the memory controller
    parameter int unsigned MctrlWidth = 64,
    /// Width of the addressable physical memory by the memory controller
    parameter int unsigned MctrlAddressWidth = 24,

    /// Number of Compute Clusters
    parameter int unsigned ComputeClusters = 1,
    /// Number of Compute Units per Cluster
    parameter int unsigned ComputeUnitsPerCluster = 1,
    /// Encoded instruction width, has to be 32
    parameter int unsigned EncInstWidth = 32,
    /// Width of the Program Counter in instructions
    parameter int unsigned PcWidth = MctrlAddressWidth - $clog2(EncInstWidth),
    /// Number of warps per compute unit
    parameter int unsigned NumWarps = 1,
    /// Number of threads per warp
    parameter int unsigned WarpWidth = 1,
    /// Number of inflight instructions per warp
    parameter int unsigned InflightInstrPerWarp = 4,
    /// How many registers can each warp access as operand or destination, has to be 8
    parameter int unsigned RegIdxWidth = 8,
    /// How many operands each instruction can have, has to be 2
    parameter int unsigned OperandsPerInst = 2,
    /// How many register banks are available
    parameter int unsigned NumBanks = 1,
    /// How many operand collectors are available
    parameter int unsigned NumOperandCollectors = 1,
    /// Should the register banks be dual ported?
    parameter bit          DualPortRegisterBanks = 1'b0,
    /// Width of the registers
    parameter int unsigned RegWidth = 32,
    // Memory Address width in bits
    parameter int unsigned AddressWidth = MctrlAddressWidth,
    // Memory Block index width -> Memory request width is 2^BlockIdxBits bytes
    parameter int unsigned BlockIdxBits = 4,
    // Width of the id for load/store requests queue -> 2^OutstandingReqIdxWidth memory requests per CU
    parameter int unsigned OutstandingReqIdxWidth = 1,
    // Number of cache lines in the instruction cache
    parameter int unsigned NumIClines = 8,
    // Number of bits for the instruction cache line index -> 2^IClineIdxBits instructions per line
    parameter int unsigned IClineIdxBits = 2,
    // How many bits are used to index thread blocks inside a thread group?
    parameter int unsigned TblockIdxBits = 8, // Determines max number of thread blocks per group
    // How many bits are used to identify a thread group?
    parameter int unsigned TgroupIdBits = 8
) (
    // Clock and reset
    input logic clk_i,
    input logic rst_ni,

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

    // I-Cacheline width in bits
    localparam int unsigned ImemDataWidth    = (1 << IClineIdxBits) * EncInstWidth;
    // I-Cacheline width in bytes
    localparam int unsigned ImemAxiStrbWidth = ImemDataWidth / 8;
    // Address in I-Cachelines
    localparam int unsigned ImemAddrWidth    = PcWidth - IClineIdxBits;
    // Address in bytes
    localparam int unsigned ImemAxiAddrWidth = PcWidth + $clog2(EncInstWidth / 8);
    // AXI ID width for the Compute Cluster IMEM
    localparam int unsigned ImemCcAxiIdWidth = ComputeUnitsPerCluster > 1
                                                ? $clog2(ComputeUnitsPerCluster) + 1 : 1;
    // AXI ID width for the instruction memory
    localparam int unsigned ImemAxiIdWidth = $clog2(ComputeClusters) + ImemCcAxiIdWidth;

    // Width of the data block address -> blockwise address
    localparam int unsigned BlockAddrWidth = AddressWidth - BlockIdxBits;
    // Width of the data block in bytes
    localparam int unsigned BlockWidth     = 1 << BlockIdxBits;

    // Width of the thread idx inside a warp
    localparam int unsigned ThreadIdxWidth = WarpWidth > 1 ? $clog2(WarpWidth) : 1;

    // Width of the memory axi id for the Compute Clusters
    localparam int unsigned MemCcAxiIdWidth = $clog2(ComputeUnitsPerCluster)
                                                + OutstandingReqIdxWidth + ThreadIdxWidth;

    // Width of the memory axi id
    localparam int unsigned MemAxiIdWidth = $clog2(ComputeClusters) + MemCcAxiIdWidth;

    // Width of the debug buses
    localparam int unsigned DbgWidth = 32;

    // OBI configuration for the debug interface
    localparam obi_pkg::obi_cfg_t DbgObiCfg = obi_pkg::obi_default_cfg(AddressWidth + 1, DbgWidth,
        MemAxiIdWidth, obi_pkg::ObiMinimalOptionalConfig);

    // With of the Memory Controller AXI ID
    localparam int unsigned MctrlAxiIdWidth = MemAxiIdWidth + 2;

    // #######################################################################################
    // # Typedefs                                                                            #
    // #######################################################################################

    typedef logic [     DbgWidth-1:0] dbg_data_t;
    typedef logic [   DbgWidth/8-1:0] dbg_be_t;
    typedef logic [ AddressWidth-1:0] addr_t;
    typedef logic [      PcWidth-1:0] pc_t;
    typedef logic [TblockIdxBits-1:0] tblock_idx_t;
    typedef logic [ TgroupIdBits-1:0] tgroup_id_t;

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

    // Instruction Memory Types
    typedef logic [ImemAddrWidth-1:0] imem_addr_t;
    typedef logic [ImemDataWidth-1:0] imem_data_t;

    typedef logic [ImemAxiStrbWidth-1:0] imem_data_strb_t;
    typedef logic [ImemAxiAddrWidth-1:0] imem_axi_addr_t;

    typedef logic [ImemCcAxiIdWidth-1:0] imem_cc_axi_id_t;
    typedef logic [  ImemAxiIdWidth-1:0] imem_axi_id_t;

    // Compute Cluster Instruction Memory AXI types
    `AXI_TYPEDEF_ALL(cc_imem_axi, imem_axi_addr_t, imem_cc_axi_id_t, imem_data_t, imem_data_strb_t,
        logic)

    // Instruction Memory AXI types
    `AXI_TYPEDEF_ALL(imem_axi, imem_axi_addr_t, imem_axi_id_t, imem_data_t, imem_data_strb_t,
        logic)

    // Instruction Memory AXI types with same ID width as the data memory
    `AXI_TYPEDEF_ALL(imem_lid_axi, imem_axi_addr_t, mem_axi_id_t, imem_data_t, imem_data_strb_t,
        logic)

    // Memory Controller types
    typedef logic [MctrlAddressWidth-1:0] mctrl_addr_t;
    typedef logic [       MctrlWidth-1:0] mctrl_data_t;
    typedef logic [     MctrlWidth/8-1:0] mctrl_strb_t;
    typedef logic [  MctrlAxiIdWidth-1:0] mctrl_axi_id_t;

    // Imem/Mem Memory Controller AXI types
    `AXI_TYPEDEF_ALL(mctrl_mem_axi, mctrl_addr_t, mem_axi_id_t, mctrl_data_t, mctrl_strb_t, logic)

    // Memory Controller AXI types
    `AXI_TYPEDEF_ALL(mctrl_axi, mctrl_addr_t, mctrl_axi_id_t, mctrl_data_t, mctrl_strb_t, logic)

    // Debug Manager OBI, Register Interface and AXI types
    `OBI_TYPEDEF_DEFAULT_ALL(dbg_obi, DbgObiCfg)
    `REG_BUS_TYPEDEF_ALL(dbg_req_reg, addr_t, dbg_data_t,
        dbg_be_t)
    `AXI_TYPEDEF_ALL(dbg_axi, addr_t, mem_axi_id_t, dbg_data_t, dbg_be_t, logic)

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Clock, reset and testmode
    logic clk, rst_n;

    // dbg req bus
    dbg_obi_req_t dbg_req_obi_req, mctrl_obi_req, thread_engine_obi_req;
    dbg_obi_rsp_t dbg_req_obi_rsp, mctrl_obi_rsp, thread_engine_obi_rsp;

    // DMI signals
    logic dmi_rst_n;

    logic [DbgWidth-1:0] dm_master_addr;

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

    imem_axi_req_t  imem_axi_req;
    imem_axi_resp_t imem_axi_rsp;

    imem_lid_axi_req_t  imem_lid_axi_req;
    imem_lid_axi_resp_t imem_lid_axi_rsp;

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

    /// Memory Controller signals
    mctrl_mem_axi_req_t  mem_mctrl_axi_req, imem_mctrl_axi_req, dbg_mctrl_axi_req;
    mctrl_mem_axi_resp_t mem_mctrl_axi_rsp, imem_mctrl_axi_rsp, dbg_mctrl_axi_rsp;

    mctrl_axi_req_t  mctrl_axi_req;
    mctrl_axi_resp_t mctrl_axi_rsp;

    // #######################################################################################
    // # Clock and Reset                                                                     #
    // #######################################################################################

    assign clk   = clk_i;
    assign rst_n = rst_ni;

    // #######################################################################################
    // # JTAG Debug Interface                                                                #
    // #######################################################################################

    dmi_jtag #(
        .IdcodeValue( 32'h00000DB3 )
    ) i_dmi_jtag (
        .clk_i     ( clk        ),
        .rst_ni    ( rst_n      ),
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

    dm_obi_top #(
        .BusWidth( DbgWidth ),
        .IdWidth ( 1        )
    ) i_dm_top (
        .clk_i     ( clk        ),
        .rst_ni    ( rst_n      ),
        .testmode_i( testmode_i ),

        .ndmreset_o   ( /* Unused */ ),
        .dmactive_o   ( /* Unused */ ),
        .debug_req_o  ( /* Unused */ ),
        .unavailable_i( 1'b0         ),
        .hartinfo_i   ( '0           ),

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

    // OBI Demux
    obi_demux #(
        .ObiCfg     ( DbgObiCfg     ),
        .obi_req_t  ( dbg_obi_req_t ),
        .obi_rsp_t  ( dbg_obi_rsp_t ),
        .NumMgrPorts( 2             ),
        .NumMaxTrans( 1             )
    ) i_obi_demux (
        .clk_i ( clk   ),
        .rst_ni( rst_n ),

        .sbr_port_select_i( dbg_req_obi_req.a.addr[AddressWidth] ),
        .sbr_port_req_i   ( dbg_req_obi_req ),
        .sbr_port_rsp_o   ( dbg_req_obi_rsp ),

        .mgr_ports_req_o( {thread_engine_obi_req, mctrl_obi_req} ),
        .mgr_ports_rsp_i( {thread_engine_obi_rsp, mctrl_obi_rsp} )
    );

    // Convert OBI request to Register Interface
    periph_to_reg #(
        .AW   ( AddressWidth      ),
        .DW   ( DbgWidth          ),
        .BW   ( 8                 ),
        .IW   ( MemAxiIdWidth     ),
        .req_t( dbg_req_reg_req_t ),
        .rsp_t( dbg_req_reg_rsp_t )
    ) i_dmi_obi_to_reg (
        .clk_i ( clk   ),
        .rst_ni( rst_n ),

        .req_i  ( mctrl_obi_req.req     ),
        .add_i  ( mctrl_obi_req.a.addr[AddressWidth-1:0] ),
        .wen_i  ( ~mctrl_obi_req.a.we   ),
        .wdata_i( mctrl_obi_req.a.wdata ),
        .be_i   ( mctrl_obi_req.a.be    ),
        .id_i   ( mctrl_obi_req.a.aid   ),

        .gnt_o    ( mctrl_obi_rsp.gnt     ),
        .r_rdata_o( mctrl_obi_rsp.r.rdata ),
        .r_opc_o  ( mctrl_obi_rsp.r.err   ),
        .r_id_o   ( mctrl_obi_rsp.r.rid   ),
        .r_valid_o( mctrl_obi_rsp.rvalid  ),

        .reg_req_o( dbg_req_reg_req ),
        .reg_rsp_i( dbg_req_reg_rsp )
    );
    assign mctrl_obi_rsp.r.r_optional = '0;

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

    // Adjust Data width to match the memory controller
    axi_dw_converter #(
        .AxiMaxReads        ( 1                       ),
        .AxiSlvPortDataWidth( DbgWidth                ),
        .AxiMstPortDataWidth( MctrlWidth              ),
        .AxiAddrWidth       ( AddressWidth            ),
        .AxiIdWidth         ( MemAxiIdWidth           ),
        .aw_chan_t          ( mctrl_mem_axi_aw_chan_t ),
        .mst_w_chan_t       ( mctrl_mem_axi_w_chan_t  ),
        .slv_w_chan_t       ( dbg_axi_w_chan_t        ),
        .b_chan_t           ( mctrl_mem_axi_b_chan_t  ),
        .ar_chan_t          ( mctrl_mem_axi_ar_chan_t ),
        .mst_r_chan_t       ( mctrl_mem_axi_r_chan_t  ),
        .slv_r_chan_t       ( dbg_axi_r_chan_t        ),
        .axi_mst_req_t      ( mctrl_mem_axi_req_t     ),
        .axi_mst_resp_t     ( mctrl_mem_axi_resp_t    ),
        .axi_slv_req_t      ( dbg_axi_req_t           ),
        .axi_slv_resp_t     ( dbg_axi_resp_t          )
    ) i_dbg_dw_conv (
        .clk_i ( clk   ),
        .rst_ni( rst_n ),

        .slv_req_i ( dbg_axi_req ),
        .slv_resp_o( dbg_axi_rsp ),

        .mst_req_o ( dbg_mctrl_axi_req ),
        .mst_resp_i( dbg_mctrl_axi_rsp )
    );

    // #######################################################################################
    // # Thread Engine                                                                       #
    // #######################################################################################

    obi_thread_engine #(
        .PcWidth      ( PcWidth       ),
        .AddressWidth ( AddressWidth  ),
        .TblockIdxBits( TblockIdxBits ),
        .TgroupIdBits ( TgroupIdBits  ),
        .ObiCfg       ( DbgObiCfg     ),
        .obi_req_t    ( dbg_obi_req_t ),
        .obi_rsp_t    ( dbg_obi_rsp_t )
    ) i_thread_engine (
        .clk_i ( clk   ),
        .rst_ni( rst_n ),

        .obi_req_i( thread_engine_obi_req ),
        .obi_rsp_o( thread_engine_obi_rsp ),

        .warp_free_i          ( warp_free              ),
        .allocate_warp_o      ( allocate_warp          ),
        .allocate_pc_o        ( cc_allocate_pc         ),
        .allocate_dp_addr_o   ( cc_allocate_dp_addr    ),
        .allocate_tblock_idx_o( cc_allocate_tblock_idx ),
        .allocate_tgroup_id_o ( cc_allocate_tgroup_id  ),

        .tblock_done_ready_o( tblock_done_ready ),
        .tblock_done_i      ( tblock_done       ),
        .tblock_done_id_i   ( tblock_done_id    )
    );

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
                cc_allocate_warp[i] = allocate_warp;
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
    // # Compute Cluster Data Memory Interconnect                                            #
    // #######################################################################################

    // Mux between Compute Clusters
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
        .clk_i ( clk        ),
        .rst_ni( rst_n      ),
        .test_i( testmode_i ),

        .slv_reqs_i ( cc_mem_axi_req ),
        .slv_resps_o( cc_mem_axi_rsp ),

        .mst_req_o ( mem_axi_req ),
        .mst_resp_i( mem_axi_rsp )
    );

    // TODO: Here we could place a data cache

    // Adjust Data width to match the memory controller
    // initial if(BlockWidth * 8 != MctrlWidth)
    //     $error("Block width (%0d) != Mctrl width (%0d), breaks yosys post_synth sim", BlockWidth * 8, MctrlWidth);

    axi_dw_converter #(
        .AxiMaxReads        ( ComputeClusters         ),
        .AxiSlvPortDataWidth( BlockWidth * 8          ),
        .AxiMstPortDataWidth( MctrlWidth              ),
        .AxiAddrWidth       ( AddressWidth            ),
        .AxiIdWidth         ( MemAxiIdWidth           ),
        .aw_chan_t          ( mctrl_mem_axi_aw_chan_t ),
        .mst_w_chan_t       ( mctrl_mem_axi_w_chan_t  ),
        .slv_w_chan_t       ( mem_axi_w_chan_t        ),
        .b_chan_t           ( mctrl_mem_axi_b_chan_t  ),
        .ar_chan_t          ( mctrl_mem_axi_ar_chan_t ),
        .mst_r_chan_t       ( mctrl_mem_axi_r_chan_t  ),
        .slv_r_chan_t       ( mem_axi_r_chan_t        ),
        .axi_mst_req_t      ( mctrl_mem_axi_req_t     ),
        .axi_mst_resp_t     ( mctrl_mem_axi_resp_t    ),
        .axi_slv_req_t      ( mem_axi_req_t           ),
        .axi_slv_resp_t     ( mem_axi_resp_t          )
    ) i_mem_dw_conv (
        .clk_i ( clk   ),
        .rst_ni( rst_n ),

        .slv_req_i ( mem_axi_req ),
        .slv_resp_o( mem_axi_rsp ),

        .mst_req_o ( mem_mctrl_axi_req ),
        .mst_resp_i( mem_mctrl_axi_rsp )
    );

    // #######################################################################################
    // # Compute Cluster Instruction Memory Interconnect                                     #
    // #######################################################################################

    axi_mux #(
        .SlvAxiIDWidth( ImemCcAxiIdWidth      ),
        .slv_aw_chan_t( cc_imem_axi_aw_chan_t ),
        .mst_aw_chan_t( imem_axi_aw_chan_t    ),
        .w_chan_t     ( cc_imem_axi_w_chan_t  ),
        .slv_b_chan_t ( cc_imem_axi_b_chan_t  ),
        .mst_b_chan_t ( imem_axi_b_chan_t     ),
        .slv_ar_chan_t( cc_imem_axi_ar_chan_t ),
        .mst_ar_chan_t( imem_axi_ar_chan_t    ),
        .slv_r_chan_t ( cc_imem_axi_r_chan_t  ),
        .mst_r_chan_t ( imem_axi_r_chan_t     ),
        .slv_req_t    ( cc_imem_axi_req_t     ),
        .slv_resp_t   ( cc_imem_axi_resp_t    ),
        .mst_req_t    ( imem_axi_req_t        ),
        .mst_resp_t   ( imem_axi_resp_t       ),
        .NoSlvPorts   ( ComputeClusters       ),
        .MaxWTrans    ( ComputeClusters       ), // This might need adjustment
        .FallThrough  ( 1'b0                  ),
        .SpillAw      ( 1'b1                  ),
        .SpillW       ( 1'b1                  ),
        .SpillB       ( 1'b1                  ),
        .SpillAr      ( 1'b1                  ),
        .SpillR       ( 1'b1                  )
    ) i_imem_mux (
        .clk_i ( clk        ),
        .rst_ni( rst_n      ),
        .test_i( testmode_i ),

        .slv_reqs_i ( cc_imem_axi_req ),
        .slv_resps_o( cc_imem_axi_rsp ),

        .mst_req_o ( imem_axi_req ),
        .mst_resp_i( imem_axi_rsp )
    );

    // Increase the ID width of the instruction memory AXI to match the data memory
    axi_id_prepend #(
        .NoBus            ( 1                      ),
        .AxiIdWidthSlvPort( ImemAxiIdWidth         ),
        .AxiIdWidthMstPort( MemAxiIdWidth          ),
        .slv_aw_chan_t    ( imem_axi_aw_chan_t     ),
        .slv_w_chan_t     ( imem_axi_w_chan_t      ),
        .slv_b_chan_t     ( imem_axi_b_chan_t      ),
        .slv_ar_chan_t    ( imem_axi_ar_chan_t     ),
        .slv_r_chan_t     ( imem_axi_r_chan_t      ),
        .mst_aw_chan_t    ( imem_lid_axi_aw_chan_t ),
        .mst_w_chan_t     ( imem_lid_axi_w_chan_t  ),
        .mst_b_chan_t     ( imem_lid_axi_b_chan_t  ),
        .mst_ar_chan_t    ( imem_lid_axi_ar_chan_t ),
        .mst_r_chan_t     ( imem_lid_axi_r_chan_t  )
    ) i_imem_id_prepend (
        .pre_id_i( '0 ),

        .slv_aw_chans_i  ( imem_axi_req.aw       ),
        .slv_aw_valids_i ( imem_axi_req.aw_valid ),
        .slv_aw_readies_o( imem_axi_rsp.aw_ready ),

        .slv_w_chans_i  ( imem_axi_req.w       ),
        .slv_w_valids_i ( imem_axi_req.w_valid ),
        .slv_w_readies_o( imem_axi_rsp.w_ready ),

        .slv_b_chans_o  ( imem_axi_rsp.b       ),
        .slv_b_valids_o ( imem_axi_rsp.b_valid ),
        .slv_b_readies_i( imem_axi_req.b_ready ),

        .slv_ar_chans_i  ( imem_axi_req.ar       ),
        .slv_ar_valids_i ( imem_axi_req.ar_valid ),
        .slv_ar_readies_o( imem_axi_rsp.ar_ready ),

        .slv_r_chans_o  ( imem_axi_rsp.r       ),
        .slv_r_valids_o ( imem_axi_rsp.r_valid ),
        .slv_r_readies_i( imem_axi_req.r_ready ),

        .mst_aw_chans_o  ( imem_lid_axi_req.aw       ),
        .mst_aw_valids_o ( imem_lid_axi_req.aw_valid ),
        .mst_aw_readies_i( imem_lid_axi_rsp.aw_ready ),

        .mst_w_chans_o  ( imem_lid_axi_req.w       ),
        .mst_w_valids_o ( imem_lid_axi_req.w_valid ),
        .mst_w_readies_i( imem_lid_axi_rsp.w_ready ),

        .mst_b_chans_i  ( imem_lid_axi_rsp.b       ),
        .mst_b_valids_i ( imem_lid_axi_rsp.b_valid ),
        .mst_b_readies_o( imem_lid_axi_req.b_ready ),

        .mst_ar_chans_o  ( imem_lid_axi_req.ar       ),
        .mst_ar_valids_o ( imem_lid_axi_req.ar_valid ),
        .mst_ar_readies_i( imem_lid_axi_rsp.ar_ready ),

        .mst_r_chans_i  ( imem_lid_axi_rsp.r       ),
        .mst_r_valids_i ( imem_lid_axi_rsp.r_valid ),
        .mst_r_readies_o( imem_lid_axi_req.r_ready )
    );

    // TODO: Here we could place an instruction cache

    // Adjust Data width to match the memory controller
    axi_dw_converter #(
        .AxiMaxReads        ( ComputeClusters         ),
        .AxiSlvPortDataWidth( ImemDataWidth           ),
        .AxiMstPortDataWidth( MctrlWidth              ),
        .AxiAddrWidth       ( ImemAddrWidth           ),
        .AxiIdWidth         ( MemAxiIdWidth           ),
        .aw_chan_t          ( mctrl_mem_axi_aw_chan_t ),
        .mst_w_chan_t       ( mctrl_mem_axi_w_chan_t  ),
        .slv_w_chan_t       ( imem_lid_axi_w_chan_t   ),
        .b_chan_t           ( mctrl_mem_axi_b_chan_t  ),
        .ar_chan_t          ( mctrl_mem_axi_ar_chan_t ),
        .mst_r_chan_t       ( mctrl_mem_axi_r_chan_t  ),
        .slv_r_chan_t       ( imem_lid_axi_r_chan_t   ),
        .axi_mst_req_t      ( mctrl_mem_axi_req_t     ),
        .axi_mst_resp_t     ( mctrl_mem_axi_resp_t    ),
        .axi_slv_req_t      ( imem_lid_axi_req_t      ),
        .axi_slv_resp_t     ( imem_lid_axi_resp_t     )
    ) i_imem_dw_conv (
        .clk_i ( clk   ),
        .rst_ni( rst_n ),

        .slv_req_i ( imem_lid_axi_req ),
        .slv_resp_o( imem_lid_axi_rsp ),

        .mst_req_o ( imem_mctrl_axi_req ),
        .mst_resp_i( imem_mctrl_axi_rsp )
    );

    // #######################################################################################
    // # Memory Controller Interconnect                                                      #
    // #######################################################################################

    // Memory Controller Mux
    axi_mux #(
        .SlvAxiIDWidth( MemAxiIdWidth           ),
        .slv_aw_chan_t( mctrl_mem_axi_aw_chan_t ),
        .mst_aw_chan_t( mctrl_axi_aw_chan_t     ),
        .w_chan_t     ( mctrl_axi_w_chan_t      ),
        .slv_b_chan_t ( mctrl_mem_axi_b_chan_t  ),
        .mst_b_chan_t ( mctrl_axi_b_chan_t      ),
        .slv_ar_chan_t( mctrl_mem_axi_ar_chan_t ),
        .mst_ar_chan_t( mctrl_axi_ar_chan_t     ),
        .slv_r_chan_t ( mctrl_mem_axi_r_chan_t  ),
        .mst_r_chan_t ( mctrl_axi_r_chan_t      ),
        .slv_req_t    ( mctrl_mem_axi_req_t     ),
        .slv_resp_t   ( mctrl_mem_axi_resp_t    ),
        .mst_req_t    ( mctrl_axi_req_t         ),
        .mst_resp_t   ( mctrl_axi_resp_t        ),
        .NoSlvPorts   ( 3                       ),
        .MaxWTrans    ( 2                       ), // This might need adjustment
        .FallThrough  ( 1'b0                    ),
        .SpillAw      ( 1'b1                    ),
        .SpillW       ( 1'b1                    ),
        .SpillB       ( 1'b1                    ),
        .SpillAr      ( 1'b1                    ),
        .SpillR       ( 1'b1                    )
    ) i_mctrl_mux (
        .clk_i ( clk        ),
        .rst_ni( rst_n      ),
        .test_i( testmode_i ),

        .slv_reqs_i ( {imem_mctrl_axi_req, mem_mctrl_axi_req, dbg_mctrl_axi_req} ),
        .slv_resps_o( {imem_mctrl_axi_rsp, mem_mctrl_axi_rsp, dbg_mctrl_axi_rsp} ),

        .mst_req_o ( mctrl_axi_req ),
        .mst_resp_i( mctrl_axi_rsp )
    );

    // TODO: Here before the memory controller we should put a Last Level Cache
`ifndef SYNTHESIS
    axi_dumper #(
        .BusName   ( "mctrl"          ),
        .LogAW     ( 1'b1             ),
        .LogAR     ( 1'b1             ),
        .LogW      ( 1'b1             ),
        .LogB      ( 1'b1             ),
        .LogR      ( 1'b1             ),
        .axi_req_t ( mctrl_axi_req_t  ),
        .axi_resp_t( mctrl_axi_resp_t )
    ) i_mctrl_monitor (
        .clk_i ( clk   ),
        .rst_ni( rst_n ),

        .axi_req_i ( mctrl_axi_req ),
        .axi_resp_i( mctrl_axi_rsp )
    );
`endif
    localparam int unsigned DummyMemAddressWidth = 10;
    logic [DummyMemAddressWidth-1:0] mem_addr;

    logic        mem_req,   mem_we,   mem_rvalid;
    mctrl_data_t mem_wdata, mem_rdata;
    mctrl_strb_t mem_strb;

    axi_to_mem #(
        .axi_req_t   ( mctrl_axi_req_t      ),
        .axi_resp_t  ( mctrl_axi_resp_t     ),
        .AddrWidth   ( DummyMemAddressWidth ),
        .DataWidth   ( MctrlWidth           ),
        .IdWidth     ( MctrlAxiIdWidth      ),
        .NumBanks    ( 1                    ),
        .BufDepth    ( 1                    ),
        .HideStrb    ( 1'b0                 ), /// This currently is buggy when enabled
        .OutFifoDepth( 1                    )
    ) i_axi_to_mem (
        .clk_i ( clk   ),
        .rst_ni( rst_n ),

        .axi_req_i ( mctrl_axi_req ),
        .axi_resp_o( mctrl_axi_rsp ),

        .mem_req_o  ( mem_req   ),
        .mem_gnt_i  ( 1'b1      ),
        .mem_addr_o ( mem_addr  ),
        .mem_we_o   ( mem_we    ),
        .mem_wdata_o( mem_wdata ),
        .mem_strb_o ( mem_strb  ),

        .mem_rvalid_i( mem_rvalid ),
        .mem_rdata_i ( mem_rdata  ),

        .busy_o    ( /* Unused */ ),
        .mem_atop_o( /* Unused */ )
    );

    tc_sram #(
        .NumWords   ( 1 << (DummyMemAddressWidth - $clog2(MctrlWidth / 8)) ),
        .DataWidth  ( MctrlWidth    ),
        .ByteWidth  ( 8             ),
        .NumPorts   ( 1             ),
        .Latency    ( 1             ),
        .SimInit    ( "zeros"       ),
        .PrintSimCfg( 1'b1          ),
        .ImplKey    ( "i_mctrl_mem" )
    ) i_mctlr_mem (
        .clk_i ( clk   ),
        .rst_ni( rst_n ),

        .req_i  ( mem_req   ),
        .we_i   ( mem_we    ),
        .addr_i ( mem_addr[DummyMemAddressWidth-1:$clog2(MctrlWidth / 8)] ),
        .wdata_i( mem_wdata ),
        .be_i   ( mem_strb  ),

        .rdata_o( mem_rdata )
    );

    `FF(mem_rvalid, mem_req, 1'b0, clk, rst_n)
endmodule : bgpu_soc
