// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "axi/typedef.svh"

/// Compute Cluster Synthesis Wrapper
// Unpacks all interfaces into simple ports
module compute_cluster_synth_wrapper #(
    /// Number of Compute Units in the cluster
    parameter int unsigned ComputeUnits = 2,
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
    // How many bits are used to identify a thread block?
    parameter int unsigned TblockIdBits = 8,

    /// Dependent parameter, do **not** overwrite.
    parameter int unsigned ImemAxiIdWidth = ComputeUnits > 1 ? $clog2(ComputeUnits) + 1 : 1,
    parameter int unsigned ImemAxiAddrWidth = PcWidth + $clog2(EncInstWidth / 8),

    parameter int unsigned ThreadIdxWidth = WarpWidth > 1 ? $clog2(WarpWidth) : 1,
    parameter int unsigned MemAxiIdWidth = $clog2(ComputeUnits) + OutstandingReqIdxWidth
                                            + ThreadIdxWidth,
    parameter int unsigned BlockWidth = 1 << BlockIdxBits,

    parameter type imem_axi_id_t   = logic [ImemAxiIdWidth-1:0],
    parameter type imem_axi_addr_t = logic [ImemAxiAddrWidth-1:0],

    parameter type imem_data_strb_t = logic [EncInstWidth * (1 << IClineIdxBits) / 8-1:0],
    parameter type imem_data_t      = logic [EncInstWidth * (1 << IClineIdxBits)    -1:0],

    parameter type mem_axi_id_t = logic [MemAxiIdWidth-1:0],
    parameter type block_data_t = logic [BlockWidth * 8 - 1:0],
    parameter type block_mask_t = logic [BlockWidth     - 1:0],

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
    output imem_axi_id_t     imem_axi_ar_id_o,
    output imem_axi_addr_t   imem_axi_ar_addr_o,
    output axi_pkg::len_t    imem_axi_ar_len_o,
    output axi_pkg::size_t   imem_axi_ar_size_o,
    output axi_pkg::burst_t  imem_axi_ar_burst_o,
    output logic             imem_axi_ar_lock_o,
    output axi_pkg::cache_t  imem_axi_ar_cache_o,
    output axi_pkg::prot_t   imem_axi_ar_prot_o,
    output axi_pkg::qos_t    imem_axi_ar_qos_o,
    output axi_pkg::region_t imem_axi_ar_region_o,
    output logic             imem_axi_ar_user_o,
    output logic             imem_axi_ar_valid_o,
    input  logic             imem_axi_ar_ready_i,

    input  imem_axi_id_t   imem_axi_r_id_i,
    input  imem_data_t     imem_axi_r_data_i,
    input  axi_pkg::resp_t imem_axi_r_resp_i,
    input  logic           imem_axi_r_last_i,
    input  logic           imem_axi_r_user_i,
    input  logic           imem_axi_r_valid_i,
    output logic           imem_axi_r_ready_o,

    output imem_axi_id_t     imem_axi_aw_id_o,
    output imem_axi_addr_t   imem_axi_aw_addr_o,
    output axi_pkg::len_t    imem_axi_aw_len_o,
    output axi_pkg::size_t   imem_axi_aw_size_o,
    output axi_pkg::burst_t  imem_axi_aw_burst_o,
    output logic             imem_axi_aw_lock_o,
    output axi_pkg::cache_t  imem_axi_aw_cache_o,
    output axi_pkg::prot_t   imem_axi_aw_prot_o,
    output axi_pkg::qos_t    imem_axi_aw_qos_o,
    output axi_pkg::region_t imem_axi_aw_region_o,
    output axi_pkg::atop_t   imem_axi_aw_atop_o,
    output logic             imem_axi_aw_user_o,
    output logic             imem_axi_aw_valid_o,
    input  logic             imem_axi_aw_ready_i,

    output imem_data_t      imem_axi_w_data_o,
    output imem_data_strb_t imem_axi_w_strb_o,
    output logic            imem_axi_w_last_o,
    output logic            imem_axi_w_user_o,
    output logic            imem_axi_w_valid_o,
    input  logic            imem_axi_w_ready_i,

    input  imem_axi_id_t   imem_axi_b_id_i,
    input  axi_pkg::resp_t imem_axi_b_resp_i,
    input  logic           imem_axi_b_user_i,
    input  logic           imem_axi_b_valid_i,
    output logic           imem_axi_b_ready_o,

    /// Memory AXI Request and Response
    output mem_axi_id_t      mem_axi_ar_id_o,
    output addr_t            mem_axi_ar_addr_o,
    output axi_pkg::len_t    mem_axi_ar_len_o,
    output axi_pkg::size_t   mem_axi_ar_size_o,
    output axi_pkg::burst_t  mem_axi_ar_burst_o,
    output logic             mem_axi_ar_lock_o,
    output axi_pkg::cache_t  mem_axi_ar_cache_o,
    output axi_pkg::prot_t   mem_axi_ar_prot_o,
    output axi_pkg::qos_t    mem_axi_ar_qos_o,
    output axi_pkg::region_t mem_axi_ar_region_o,
    output logic             mem_axi_ar_user_o,
    output logic             mem_axi_ar_valid_o,
    input  logic             mem_axi_ar_ready_i,

    input  mem_axi_id_t    mem_axi_r_id_i,
    input  block_data_t    mem_axi_r_data_i,
    input  axi_pkg::resp_t mem_axi_r_resp_i,
    input  logic           mem_axi_r_last_i,
    input  logic           mem_axi_r_user_i,
    input  logic           mem_axi_r_valid_i,
    output logic           mem_axi_r_ready_o,

    output mem_axi_id_t      mem_axi_aw_id_o,
    output addr_t            mem_axi_aw_addr_o,
    output axi_pkg::len_t    mem_axi_aw_len_o,
    output axi_pkg::size_t   mem_axi_aw_size_o,
    output axi_pkg::burst_t  mem_axi_aw_burst_o,
    output logic             mem_axi_aw_lock_o,
    output axi_pkg::cache_t  mem_axi_aw_cache_o,
    output axi_pkg::prot_t   mem_axi_aw_prot_o,
    output axi_pkg::qos_t    mem_axi_aw_qos_o,
    output axi_pkg::region_t mem_axi_aw_region_o,
    output axi_pkg::atop_t   mem_axi_aw_atop_o,
    output logic             mem_axi_aw_user_o,
    output logic             mem_axi_aw_valid_o,
    input  logic             mem_axi_aw_ready_i,

    output block_data_t mem_axi_w_data_o,
    output block_mask_t mem_axi_w_strb_o,
    output logic        mem_axi_w_last_o,
    output logic        mem_axi_w_user_o,
    output logic        mem_axi_w_valid_o,
    input  logic        mem_axi_w_ready_i,

    input  mem_axi_id_t    mem_axi_b_id_i,
    input  axi_pkg::resp_t mem_axi_b_resp_i,
    input  logic           mem_axi_b_user_i,
    input  logic           mem_axi_b_valid_i,
    output logic           mem_axi_b_ready_o
);

    `AXI_TYPEDEF_ALL(imem_axi, imem_axi_addr_t, imem_axi_id_t, imem_data_t, imem_data_strb_t,
        logic)

    `AXI_TYPEDEF_ALL(mem_axi, addr_t, mem_axi_id_t, block_data_t, block_mask_t, logic)

    imem_axi_req_t  imem_axi_req;
    imem_axi_resp_t imem_axi_rsp;

    mem_axi_req_t  mem_axi_req;
    mem_axi_resp_t mem_axi_rsp;

    assign imem_axi_ar_id_o     = imem_axi_req.ar.id;
    assign imem_axi_ar_addr_o   = imem_axi_req.ar.addr;
    assign imem_axi_ar_len_o    = imem_axi_req.ar.len;
    assign imem_axi_ar_size_o   = imem_axi_req.ar.size;
    assign imem_axi_ar_burst_o  = imem_axi_req.ar.burst;
    assign imem_axi_ar_lock_o   = imem_axi_req.ar.lock;
    assign imem_axi_ar_cache_o  = imem_axi_req.ar.cache;
    assign imem_axi_ar_prot_o   = imem_axi_req.ar.prot;
    assign imem_axi_ar_qos_o    = imem_axi_req.ar.qos;
    assign imem_axi_ar_region_o = imem_axi_req.ar.region;
    assign imem_axi_ar_user_o   = imem_axi_req.ar.user;
    assign imem_axi_ar_valid_o  = imem_axi_req.ar_valid;
    assign imem_axi_r_ready_o   = imem_axi_req.r_ready;

    assign imem_axi_rsp.ar_ready = imem_axi_ar_ready_i;
    assign imem_axi_rsp.r.id     = imem_axi_r_id_i;
    assign imem_axi_rsp.r.data   = imem_axi_r_data_i;
    assign imem_axi_rsp.r.resp   = imem_axi_r_resp_i;
    assign imem_axi_rsp.r.last   = imem_axi_r_last_i;
    assign imem_axi_rsp.r.user   = imem_axi_r_user_i;
    assign imem_axi_rsp.r_valid  = imem_axi_r_valid_i;

    assign imem_axi_aw_id_o     = imem_axi_req.aw.id;
    assign imem_axi_aw_addr_o   = imem_axi_req.aw.addr;
    assign imem_axi_aw_len_o    = imem_axi_req.aw.len;
    assign imem_axi_aw_size_o   = imem_axi_req.aw.size;
    assign imem_axi_aw_burst_o  = imem_axi_req.aw.burst;
    assign imem_axi_aw_lock_o   = imem_axi_req.aw.lock;
    assign imem_axi_aw_cache_o  = imem_axi_req.aw.cache;
    assign imem_axi_aw_prot_o   = imem_axi_req.aw.prot;
    assign imem_axi_aw_qos_o    = imem_axi_req.aw.qos;
    assign imem_axi_aw_region_o = imem_axi_req.aw.region;
    assign imem_axi_aw_atop_o   = imem_axi_req.aw.atop;
    assign imem_axi_aw_user_o   = imem_axi_req.aw.user;
    assign imem_axi_aw_valid_o  = imem_axi_req.aw_valid;
    assign imem_axi_w_data_o    = imem_axi_req.w.data;
    assign imem_axi_w_strb_o    = imem_axi_req.w.strb;
    assign imem_axi_w_last_o    = imem_axi_req.w.last;
    assign imem_axi_w_user_o    = imem_axi_req.w.user;
    assign imem_axi_w_valid_o   = imem_axi_req.w_valid;
    assign imem_axi_b_ready_o   = imem_axi_req.b_ready;

    assign imem_axi_rsp.aw_ready = imem_axi_aw_ready_i;
    assign imem_axi_rsp.w_ready  = imem_axi_w_ready_i;
    assign imem_axi_rsp.b.id     = imem_axi_b_id_i;
    assign imem_axi_rsp.b.resp   = imem_axi_b_resp_i;
    assign imem_axi_rsp.b.user   = imem_axi_b_user_i;
    assign imem_axi_rsp.b_valid  = imem_axi_b_valid_i;

    assign mem_axi_ar_id_o     = mem_axi_req.ar.id;
    assign mem_axi_ar_addr_o   = mem_axi_req.ar.addr;
    assign mem_axi_ar_len_o    = mem_axi_req.ar.len;
    assign mem_axi_ar_size_o   = mem_axi_req.ar.size;
    assign mem_axi_ar_burst_o  = mem_axi_req.ar.burst;
    assign mem_axi_ar_lock_o   = mem_axi_req.ar.lock;
    assign mem_axi_ar_cache_o  = mem_axi_req.ar.cache;
    assign mem_axi_ar_prot_o   = mem_axi_req.ar.prot;
    assign mem_axi_ar_qos_o    = mem_axi_req.ar.qos;
    assign mem_axi_ar_region_o = mem_axi_req.ar.region;
    assign mem_axi_ar_user_o   = mem_axi_req.ar.user;
    assign mem_axi_ar_valid_o  = mem_axi_req.ar_valid;
    assign mem_axi_r_ready_o   = mem_axi_req.r_ready;

    assign mem_axi_rsp.ar_ready = mem_axi_ar_ready_i;
    assign mem_axi_rsp.r.id     = mem_axi_r_id_i;
    assign mem_axi_rsp.r.data   = mem_axi_r_data_i;
    assign mem_axi_rsp.r.resp   = mem_axi_r_resp_i;
    assign mem_axi_rsp.r.last   = mem_axi_r_last_i;
    assign mem_axi_rsp.r.user   = mem_axi_r_user_i;
    assign mem_axi_rsp.r_valid  = mem_axi_r_valid_i;

    assign mem_axi_aw_id_o     = mem_axi_req.aw.id;
    assign mem_axi_aw_addr_o   = mem_axi_req.aw.addr;
    assign mem_axi_aw_len_o    = mem_axi_req.aw.len;
    assign mem_axi_aw_size_o   = mem_axi_req.aw.size;
    assign mem_axi_aw_burst_o  = mem_axi_req.aw.burst;
    assign mem_axi_aw_lock_o   = mem_axi_req.aw.lock;
    assign mem_axi_aw_cache_o  = mem_axi_req.aw.cache;
    assign mem_axi_aw_prot_o   = mem_axi_req.aw.prot;
    assign mem_axi_aw_qos_o    = mem_axi_req.aw.qos;
    assign mem_axi_aw_region_o = mem_axi_req.aw.region;
    assign mem_axi_aw_atop_o   = mem_axi_req.aw.atop;
    assign mem_axi_aw_user_o   = mem_axi_req.aw.user;
    assign mem_axi_aw_valid_o  = mem_axi_req.aw_valid;
    assign mem_axi_w_data_o    = mem_axi_req.w.data;
    assign mem_axi_w_strb_o    = mem_axi_req.w.strb;
    assign mem_axi_w_last_o    = mem_axi_req.w.last;
    assign mem_axi_w_user_o    = mem_axi_req.w.user;
    assign mem_axi_w_valid_o   = mem_axi_req.w_valid;
    assign mem_axi_b_ready_o   = mem_axi_req.b_ready;

    assign mem_axi_rsp.aw_ready = mem_axi_aw_ready_i;
    assign mem_axi_rsp.w_ready  = mem_axi_w_ready_i;
    assign mem_axi_rsp.b.id     = mem_axi_b_id_i;
    assign mem_axi_rsp.b.resp   = mem_axi_b_resp_i;
    assign mem_axi_rsp.b.user   = mem_axi_b_user_i;
    assign mem_axi_rsp.b_valid  = mem_axi_b_valid_i;

    compute_cluster #(
        .ComputeUnits          ( ComputeUnits           ),
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
        .TblockIdBits          ( TblockIdBits           ),

        .imem_axi_req_t ( imem_axi_req_t  ),
        .imem_axi_resp_t( imem_axi_resp_t ),

        .mem_axi_req_t ( mem_axi_req_t  ),
        .mem_axi_resp_t( mem_axi_resp_t )
    ) i_cc (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .warp_free_o          ( warp_free_o           ),
        .allocate_warp_i      ( allocate_warp_i       ),
        .allocate_pc_i        ( allocate_pc_i         ),
        .allocate_dp_addr_i   ( allocate_dp_addr_i    ),
        .allocate_tblock_idx_i( allocate_tblock_idx_i ),
        .allocate_tblock_id_i ( allocate_tblock_id_i  ),

        .tblock_done_ready_i( tblock_done_ready_i ),
        .tblock_done_o      ( tblock_done_o       ),
        .tblock_done_id_o   ( tblock_done_id_o    ),

        .imem_req_o( imem_axi_req ),
        .imem_rsp_i( imem_axi_rsp ),

        .mem_req_o ( mem_axi_req ),
        .mem_rsp_i ( mem_axi_rsp )
    );

endmodule : compute_cluster_synth_wrapper
