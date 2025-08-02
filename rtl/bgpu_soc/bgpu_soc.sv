// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "axi/typedef.svh"

`include "common_cells/registers.svh"

/// BGPU SoC top-level module
// Contains:
// - Control Domain
// - Compute Clusters
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
    parameter int unsigned WarpWidth = 4,
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

    // Width of the control domain buses
    localparam int unsigned CtrlWidth = 32;

    // With of the Memory Controller AXI ID
    localparam int unsigned MctrlAxiIdWidth = MemAxiIdWidth + 2;

    // #######################################################################################
    // # Typedefs                                                                            #
    // #######################################################################################

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

    // Control Domain AXI types
    typedef logic [  CtrlWidth-1:0] ctrl_data_t;
    typedef logic [CtrlWidth/8-1:0] ctrl_be_t;

    `AXI_TYPEDEF_ALL(ctrl_axi, addr_t, mem_axi_id_t, ctrl_data_t, ctrl_be_t, logic)

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Clock and Reset from Control Domain
    logic clk, rst_n;

    // Flush instruction cache
    logic flush_ic;

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

    // Control Domain AXI
    ctrl_axi_req_t  ctrl_axi_req;
    ctrl_axi_resp_t ctrl_axi_rsp;

    /// Memory Controller signals
    mctrl_mem_axi_req_t  mem_mctrl_axi_req, imem_mctrl_axi_req, ctrl_mctrl_axi_req;
    mctrl_mem_axi_resp_t mem_mctrl_axi_rsp, imem_mctrl_axi_rsp, ctrl_mctrl_axi_rsp;

    mctrl_axi_req_t  mctrl_axi_req;
    mctrl_axi_resp_t mctrl_axi_rsp;

    // #######################################################################################
    // # Control Domain                                                                      #
    // #######################################################################################

    control_domain #(
        .CtrlWidth    ( CtrlWidth     ),
        .AxiIdWidth   ( MemAxiIdWidth ),
        .PcWidth      ( PcWidth       ),
        .AddressWidth ( AddressWidth  ),
        .TblockIdxBits( TblockIdxBits ),
        .TgroupIdBits ( TgroupIdBits  ),

        .axi_req_t ( ctrl_axi_req_t  ),
        .axi_resp_t( ctrl_axi_resp_t )
    ) i_ctrl_domain (
        .clk_i ( clk_i  ),
        .clk_o ( clk    ),
        .rst_ni( rst_ni ),
        .rst_no( rst_n  ),

        .testmode_i( testmode_i ),

        .flush_ic_o( flush_ic ),

        .jtag_tck_i  ( jtag_tck_i   ),
        .jtag_tdi_i  ( jtag_tdi_i   ),
        .jtag_tdo_o  ( jtag_tdo_o   ),
        .jtag_tms_i  ( jtag_tms_i   ),
        .jtag_trst_ni( jtag_trst_ni ),

        .warp_free_i          ( warp_free              ),
        .allocate_warp_o      ( allocate_warp          ),
        .allocate_pc_o        ( cc_allocate_pc         ),
        .allocate_dp_addr_o   ( cc_allocate_dp_addr    ),
        .allocate_tblock_idx_o( cc_allocate_tblock_idx ),
        .allocate_tgroup_id_o ( cc_allocate_tgroup_id  ),

        .tblock_done_ready_o( tblock_done_ready ),
        .tblock_done_i      ( tblock_done       ),
        .tblock_done_id_i   ( tblock_done_id    ),

        .axi_req_o( ctrl_axi_req ),
        .axi_rsp_i( ctrl_axi_rsp )
    );

    // #######################################################################################
    // # Adjust AXI width of Control Domain                                                  #
    // #######################################################################################

    axi_dw_converter #(
        .AxiMaxReads        ( 1                       ),
        .AxiSlvPortDataWidth( CtrlWidth               ),
        .AxiMstPortDataWidth( MctrlWidth              ),
        .AxiAddrWidth       ( AddressWidth            ),
        .AxiIdWidth         ( MemAxiIdWidth           ),
        .aw_chan_t          ( mctrl_mem_axi_aw_chan_t ),
        .mst_w_chan_t       ( mctrl_mem_axi_w_chan_t  ),
        .slv_w_chan_t       ( ctrl_axi_w_chan_t       ),
        .b_chan_t           ( mctrl_mem_axi_b_chan_t  ),
        .ar_chan_t          ( mctrl_mem_axi_ar_chan_t ),
        .mst_r_chan_t       ( mctrl_mem_axi_r_chan_t  ),
        .slv_r_chan_t       ( ctrl_axi_r_chan_t       ),
        .axi_mst_req_t      ( mctrl_mem_axi_req_t     ),
        .axi_mst_resp_t     ( mctrl_mem_axi_resp_t    ),
        .axi_slv_req_t      ( ctrl_axi_req_t          ),
        .axi_slv_resp_t     ( ctrl_axi_resp_t         )
    ) i_ctrl_dw_conv (
        .clk_i ( clk   ),
        .rst_ni( rst_n ),

        .slv_req_i ( ctrl_axi_req ),
        .slv_resp_o( ctrl_axi_rsp ),

        .mst_req_o ( ctrl_mctrl_axi_req ),
        .mst_resp_i( ctrl_mctrl_axi_rsp )
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
            .ClusterId             ( i                      ),

            .imem_axi_req_t ( cc_imem_axi_req_t  ),
            .imem_axi_resp_t( cc_imem_axi_resp_t ),

            .mem_axi_req_t ( cc_mem_axi_req_t  ),
            .mem_axi_resp_t( cc_mem_axi_resp_t )
        ) i_cc (
            .clk_i ( clk   ),
            .rst_ni( rst_n ),

            .testmode_i( testmode_i ),

            .flush_ic_i( flush_ic ),

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

        .slv_reqs_i ( {imem_mctrl_axi_req, mem_mctrl_axi_req, ctrl_mctrl_axi_req} ),
        .slv_resps_o( {imem_mctrl_axi_rsp, mem_mctrl_axi_rsp, ctrl_mctrl_axi_rsp} ),

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
