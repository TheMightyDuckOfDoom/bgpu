// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "axi/typedef.svh"

/// Compute Cluster
// Contains:
// - Multiple Compute Units
module compute_cluster #(
    /// Number of Compute Units in the cluster
    parameter int unsigned ComputeUnits = 1,
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
    // Memory Block size in bytes -> Memory request width
    parameter int unsigned BlockIdxBits = 4,
    // Width of the id for requests queue
    parameter int unsigned OutstandingReqIdxWidth = 3,
    // Number of cache lines in the instruction cache
    parameter int unsigned NumIClines = 8,
    // Number of bits for the instruction cache line index
    parameter int unsigned IClineIdxBits = 2,
    // How many bits are used to index thread blocks inside a thread group?
    parameter int unsigned TblockIdxBits = 8,
    // How many bits are used to identify a thread block?
    parameter int unsigned TblockIdBits = 8,

    // Instruction Memory AXI Request and Response types
    parameter type imem_axi_req_t  = logic,
    parameter type imem_axi_resp_t = logic,

    /// Dependent parameter, do **not** overwrite.
    parameter type tblock_idx_t = logic [TblockIdxBits-1:0],
    parameter type tblock_id_t  = logic [ TblockIdBits-1:0],
    parameter type addr_t       = logic [ AddressWidth-1:0],
    parameter type pc_t         = logic [      PcWidth-1:0]
) (
    /// Clock and reset
    input  logic clk_i,
    input  logic rst_ni,

    // Interface to start a new thread block on this compute cluster
    output logic        warp_free_o, // The is atleas one free warp that can start a new block
    input  logic        allocate_warp_i,
    input  pc_t         allocate_pc_i,
    input  addr_t       allocate_dp_addr_i, // Data / Parameter address
    input  tblock_idx_t allocate_tblock_idx_i, // Block index -> used to calculate the thread id
    input  tblock_id_t  allocate_tblock_id_i,  // Block id -> unique identifier for the block

    // Thread block completion
    input  logic       tblock_done_ready_i,
    output logic       tblock_done_o,
    output tblock_id_t tblock_done_id_o,

    /// Instruction Memory AXI Request and Response
    output imem_axi_req_t  imem_req_o,
    input  imem_axi_resp_t imem_rsp_i
);

    // I-Cacheline width in bits
    localparam int unsigned ImemDataWidth    = (1 << IClineIdxBits) * EncInstWidth;
    // I-Cacheline width in bytes
    localparam int unsigned ImemAxiStrbWidth = ImemDataWidth / 8;
    // Address in I-Cachelines
    localparam int unsigned ImemAddrWidth    = PcWidth - IClineIdxBits;
    // Address in bytes
    localparam int unsigned ImemAxiAddrWidth = PcWidth + $clog2(EncInstWidth / 8);
    // AXI ID width for the Compute Unit IMEM
    localparam int unsigned ImemCcAxiIdWidth = ComputeUnits > 1 ? $clog2(ComputeUnits) + 1 : 1;

    // #######################################################################################
    // # Typedefs                                                                            #
    // #######################################################################################

    typedef logic [ImemAddrWidth-1:0] imem_addr_t;
    typedef logic [ImemDataWidth-1:0] imem_data_t;

    typedef logic [ImemAxiStrbWidth-1:0] imem_data_strb_t;
    typedef logic [ImemAxiAddrWidth-1:0] imem_axi_addr_t;

    typedef logic [ImemCcAxiIdWidth-1:0] imem_cc_axi_id_t;

    `AXI_TYPEDEF_ALL(cu_imem_axi, imem_axi_addr_t, logic[0:0],       imem_data_t, imem_data_strb_t,
        logic)
    `AXI_TYPEDEF_ALL(cc_imem_axi, imem_axi_addr_t, imem_cc_axi_id_t, imem_data_t, imem_data_strb_t,
        logic)

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Compute Unit thread block distribution
    logic       [ComputeUnits-1:0] cu_allocate, cu_warp_free;

    // Compute Unit thread block completion
    logic       [ComputeUnits-1:0] cu_done_ready, cu_done;
    tblock_id_t [ComputeUnits-1:0] cu_done_id;

    // IMEM AXI
    cu_imem_axi_req_t  [ComputeUnits-1:0] cu_imem_axi_req;
    cu_imem_axi_resp_t [ComputeUnits-1:0] cu_imem_axi_rsp;

    // Compute Unit IMEM
    logic       [ComputeUnits-1:0] imem_req_valid, imem_ready, imem_rsp_valid;
    imem_addr_t [ComputeUnits-1:0] imem_req_addr;
    imem_data_t [ComputeUnits-1:0] imem_rsp_data;

    // #######################################################################################
    // # Data Cache and AXI Adapter                                                          #
    // #######################################################################################

    // #######################################################################################
    // # Compute Units IMEM to AXI - Adapter and Multiplexer                                 #
    // #######################################################################################

    axi_mux #(
        .SlvAxiIDWidth ( 1                      ),
        .slv_aw_chan_t ( cu_imem_axi_aw_chan_t  ),
        .mst_aw_chan_t ( cc_imem_axi_aw_chan_t  ),
        .w_chan_t      ( cu_imem_axi_w_chan_t   ),
        .slv_b_chan_t  ( cu_imem_axi_b_chan_t   ),
        .mst_b_chan_t  ( cc_imem_axi_b_chan_t   ),
        .slv_ar_chan_t ( cu_imem_axi_ar_chan_t  ),
        .mst_ar_chan_t ( cc_imem_axi_ar_chan_t  ),
        .slv_r_chan_t  ( cu_imem_axi_r_chan_t   ),
        .mst_r_chan_t  ( cc_imem_axi_r_chan_t   ),
        .slv_req_t     ( cu_imem_axi_req_t      ),
        .slv_resp_t    ( cu_imem_axi_resp_t     ),
        .mst_req_t     ( cc_imem_axi_req_t      ),
        .mst_resp_t    ( cc_imem_axi_resp_t     ),
        .NoSlvPorts    ( ComputeUnits           ),
        .MaxWTrans     ( 1                      ),
        .FallThrough   ( 1'b1                   ),
        .SpillAw       ( 1'b0                   ),
        .SpillW        ( 1'b0                   ),
        .SpillB        ( 1'b0                   ),
        .SpillAr       ( 1'b0                   ),
        .SpillR        ( 1'b0                   )
    ) i_imem_mux (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),
        .test_i( 1'b0   ),

        .slv_reqs_i ( cu_imem_axi_req ),
        .slv_resps_o( cu_imem_axi_rsp ),

        .mst_req_o ( imem_req_o ),
        .mst_resp_i( imem_rsp_i )
    );

    for(genvar cu = 0; cu < ComputeUnits; cu++) begin : gen_imem_to_axi
        imem_to_axi #(
            .axi_req_t  ( cu_imem_axi_req_t  ),
            .axi_rsp_t  ( cu_imem_axi_resp_t ),
            .axi_addr_t ( imem_axi_addr_t    ),
            .imem_addr_t( imem_addr_t        ),
            .imem_data_t( imem_data_t        )
        ) i_imem_to_obi (
            .imem_ready_o    ( imem_ready    [cu] ),
            .imem_req_valid_i( imem_req_valid[cu] ),
            .imem_req_addr_i ( imem_req_addr [cu] ),

            .imem_rsp_valid_o( imem_rsp_valid[cu] ),
            .imem_rsp_data_o ( imem_rsp_data [cu] ),

            .axi_req_o( cu_imem_axi_req[cu] ),
            .axi_rsp_i( cu_imem_axi_rsp[cu] )
        );
    end : gen_imem_to_axi

    // #######################################################################################
    // # Thread Block distribution                                                           #
    // #######################################################################################

    // Atleast one warp is free in the cluster
    assign warp_free_o = |cu_warp_free;

    always_comb begin : distribute_thread_block
        // Default: No Compute Unit is selected
        cu_allocate = '0;

        // If a warp is free, allocate it to the Compute Unit
        if (allocate_warp_i) begin
            for (int unsigned cu = 0; cu < ComputeUnits; cu++) begin
                if (cu_warp_free[cu]) begin
                    cu_allocate[cu] = 1'b1;
                    break; // Only allocate to the first free CU
                end
            end
        end
    end : distribute_thread_block

    // Thread block completion
    stream_arbiter #(
        .DATA_T   ( tblock_id_t ),
        .N_INP    ( ComputeUnits ),
        .ARBITER  ( "rr"         )
    ) i_tblock_done_arbiter (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .inp_data_i ( cu_done_id    ),
        .inp_valid_i( cu_done       ),
        .inp_ready_o( cu_done_ready ),

        .oup_data_o ( tblock_done_id_o    ),
        .oup_valid_o( tblock_done_o       ),
        .oup_ready_i( tblock_done_ready_i )
    );

    // #######################################################################################
    // # Compute Units                                                                       #
    // #######################################################################################

    for(genvar cu = 0; cu < ComputeUnits; cu++) begin : gen_compute_units
        compute_unit #(
            .PcWidth               ( PcWidth                ),
            .NumWarps              ( NumWarps               ),
            .WarpWidth             ( WarpWidth              ),
            .EncInstWidth          ( EncInstWidth           ),
            .InflightInstrPerWarp  ( InflightInstrPerWarp   ),
            .RegIdxWidth           ( RegIdxWidth            ),
            .OperandsPerInst       ( OperandsPerInst        ),
            .NumBanks              ( NumBanks               ),
            .NumOperandCollectors  ( NumOperandCollectors   ),
            .RegWidth              ( RegWidth               ),
            .AddressWidth          ( AddressWidth           ),
            .BlockIdxBits          ( BlockIdxBits           ),
            .OutstandingReqIdxWidth( OutstandingReqIdxWidth ),
            .NumIClines            ( NumIClines             ),
            .IClineIdxBits         ( IClineIdxBits          ),
            .TblockIdxBits         ( TblockIdxBits          ),
            .TblockIdBits          ( TblockIdBits           )
        ) i_cu (
            .clk_i ( clk_i  ),
            .rst_ni( rst_ni ),

            .warp_free_o          ( cu_warp_free[cu]      ),
            .allocate_warp_i      ( cu_allocate [cu]      ),
            .allocate_pc_i        ( allocate_pc_i         ),
            .allocate_dp_addr_i   ( allocate_dp_addr_i    ),
            .allocate_tblock_idx_i( allocate_tblock_idx_i ),
            .allocate_tblock_id_i ( allocate_tblock_id_i  ),

            .tblock_done_ready_i( cu_done_ready[cu] ),
            .tblock_done_o      ( cu_done      [cu] ),
            .tblock_done_id_o   ( cu_done_id   [cu] ),

            .imem_ready_i    ( imem_ready    [cu] ),
            .imem_req_valid_o( imem_req_valid[cu] ),
            .imem_req_addr_o ( imem_req_addr [cu] ),

            .imem_rsp_valid_i( imem_rsp_valid[cu] ),
            .imem_rsp_data_i ( imem_rsp_data [cu] ),

            .mem_ready_i      (  ),
            .mem_req_valid_o  (  ),
            .mem_req_id_o     (  ),
            .mem_req_addr_o   (  ),
            .mem_req_we_mask_o(  ),
            .mem_req_wdata_o  (  ),

            .mem_rsp_valid_i(  ),
            .mem_rsp_id_i   (  ),
            .mem_rsp_data_i (  )
        );
    end : gen_compute_units

endmodule : compute_cluster
