// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "common_cells/registers.svh"

/// Compute Unit
module compute_unit import bgpu_pkg::*; #(
    /// Number of instructions to fetch for the warp
    parameter int unsigned FetchWidth = 1,
    /// Number of instructions that can write back simultaneously
    parameter int unsigned WritebackWidth = 1,
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
    // How many bits are used to identify a thread group?
    parameter int unsigned TgroupIdBits = 8,

    // Compute Cluster this Compute Unit is part of
    parameter int unsigned ClusterId = 0,
    // Compute Unit ID inside the Compute Cluster
    parameter int unsigned ComputeUnitId = 0,

    /// Dependent parameter, do **not** overwrite.
    parameter int unsigned BlockAddrWidth  = AddressWidth - BlockIdxBits,
    parameter int unsigned BlockWidth      = 1 << BlockIdxBits, // In bytes
    parameter int unsigned ThreadIdxWidth  = WarpWidth > 1 ? $clog2(WarpWidth) : 1,
    parameter int unsigned ICAddrWidth     = IClineIdxBits > 0 ? PcWidth - IClineIdxBits : PcWidth,
    parameter type tblock_idx_t = logic      [       TblockIdxBits-1:0],
    parameter type tgroup_id_t  = logic      [        TgroupIdBits-1:0],
    parameter type addr_t       = logic      [        AddressWidth-1:0],
    parameter type imem_addr_t  = logic      [         ICAddrWidth-1:0],
    parameter type enc_inst_t   = logic      [        EncInstWidth-1:0],
    parameter type imem_data_t  = enc_inst_t [(1 << IClineIdxBits)-1:0],
    parameter type pc_t         = logic      [             PcWidth-1:0],
    parameter type block_addr_t = logic      [      BlockAddrWidth-1:0],
    parameter type byte_t       = logic      [                     7:0],
    parameter type block_data_t = byte_t     [          BlockWidth-1:0],
    parameter type block_idx_t  = logic      [        BlockIdxBits-1:0],
    parameter type block_mask_t = logic      [          BlockWidth-1:0],
    parameter type req_id_t     = logic      [OutstandingReqIdxWidth + ThreadIdxWidth-1:0]
) (
    // Clock and reset
    input logic clk_i,
    input logic rst_ni,

    /// Force instructions to execute in-order
    input  logic inorder_execution_i,

    // Testmode
    input logic testmode_i,

    // Flush instruction cache
    input logic flush_ic_i,

    // Interface to start a new thread block on this compute unit
    output logic        warp_free_o, // The is atleas one free warp that can start a new block
    input  logic        allocate_warp_i,
    input  pc_t         allocate_pc_i,
    input  addr_t       allocate_dp_addr_i, // Data / Parameter address
    input  tblock_idx_t allocate_tblock_idx_i, // Block index -> used to calculate the thread id
    input  tgroup_id_t  allocate_tgroup_id_i,  // Block id -> unique identifier for the block

    // Thread block completion
    input  logic       tblock_done_ready_i,
    output logic       tblock_done_o,
    output tgroup_id_t tblock_done_id_o,

    /// Instruction Memory Request
    input  logic       imem_ready_i,
    output logic       imem_req_valid_o,
    output imem_addr_t imem_req_addr_o,

    /// Instruction Memory Response
    input  logic       imem_rsp_valid_i,
    input  imem_data_t imem_rsp_data_i,

    /// Memory Request
    input  logic        mem_ready_i,
    output logic        mem_req_valid_o,
    output req_id_t     mem_req_id_o,
    output block_addr_t mem_req_addr_o,
    output block_mask_t mem_req_we_mask_o,
    output block_data_t mem_req_wdata_o,

    /// Memory Response
    input  logic        mem_rsp_valid_i,
    input  req_id_t     mem_rsp_id_i,
    input  block_data_t mem_rsp_data_i
);
    // #######################################################################################
    // # Local Parameters                                                                    #
    // #######################################################################################

    localparam int unsigned NumTags        = InflightInstrPerWarp;
    localparam int unsigned WidWidth       =  NumWarps > 1 ? $clog2(NumWarps)  : 1;
    localparam int unsigned TagWidth       =   NumTags > 1 ? $clog2(NumTags)   : 1;
    localparam int unsigned SubwarpIdWidth = WarpWidth > 1 ? $clog2(WarpWidth) : 1;

    // #######################################################################################
    // # Typedefs                                                                            #
    // #######################################################################################

    // Typedefs
    typedef logic     [         RegIdxWidth-1:0] reg_idx_t;
    typedef logic     [ WidWidth + TagWidth-1:0] iid_t;
    typedef logic     [           WarpWidth-1:0] act_mask_t;
    typedef logic     [RegWidth * WarpWidth-1:0] warp_data_t;
    typedef logic     [            WidWidth-1:0] wid_t;
    typedef logic     [      SubwarpIdWidth-1:0] subwarp_id_t;
    typedef logic     [          FetchWidth-1:0] fetch_mask_t;
    typedef logic     [     OperandsPerInst-1:0] op_is_reg_t;
    typedef reg_idx_t [     OperandsPerInst-1:0] op_reg_idx_t;

    // Fetcher to Instruction Cache type
    typedef struct packed {
        fetch_mask_t fetch_mask;
        pc_t         pc;
        act_mask_t   act_mask;
        wid_t        warp_id;
        subwarp_id_t subwarp_id;
    } fe_to_ic_data_t;

    // Instruction Cache to Decoder type
    typedef struct packed {
        fetch_mask_t fetch_mask;
        pc_t         pc;
        act_mask_t   act_mask;
        wid_t        warp_id;
        subwarp_id_t subwarp_id;
        enc_inst_t [FetchWidth-1:0] inst;
    } ic_to_dec_data_t;

    // Decoder to Instruction Buffer type
    typedef struct packed {
        pc_t         pc;
        act_mask_t   act_mask;
        wid_t        warp_id;
        subwarp_id_t subwarp_id;
        logic        [FetchWidth-1:0] valid_insts;
        inst_t       [FetchWidth-1:0] inst;
        reg_idx_t    [FetchWidth-1:0] dst;
        op_is_reg_t  [FetchWidth-1:0] operands_is_reg;
        op_reg_idx_t [FetchWidth-1:0] operands;
    } dec_to_ib_data_t;

    // Multi Warp Dispatcher to Register Operand Collector Stage type
    typedef struct packed {
        iid_t      tag;
        pc_t       pc;
        act_mask_t act_mask;
        inst_t     inst;
        reg_idx_t  dst;
        logic      [OperandsPerInst-1:0] operands_is_reg;
        reg_idx_t  [OperandsPerInst-1:0] operands;
    } disp_to_opc_data_t;

    // Register Operand Collector Stage to Execution Units type
    typedef struct packed {
        iid_t       tag;
        pc_t        pc;
        act_mask_t  act_mask;
        inst_t      inst;
        reg_idx_t   dst;
        warp_data_t [OperandsPerInst-1:0] operands;
    } opc_to_eu_data_t;

    // Execution Units to Register Operand Collector Stage type
    typedef struct packed {
        iid_t       tag;
        act_mask_t  act_mask;
        reg_idx_t   dst;
        warp_data_t data;
    } eu_to_opc_data_t;
    
    // Result Collector mask type
    typedef logic [3:0] rc_mask_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Fetcher to Instruction Cache
    logic fe_to_ic_valid_d, fe_to_ic_valid_q;
    logic ic_to_fe_ready_d, ic_to_fe_ready_q;
    fe_to_ic_data_t fe_to_ic_data_d, fe_to_ic_data_q;

    // Fetcher to Integer Unit -> Constants per Warp
    addr_t       [NumWarps-1:0] fe_to_iu_warp_dp_addr;    // Data / Parameter address
    tblock_idx_t [NumWarps-1:0] fe_to_iu_warp_tblock_idx; // Block index

    /// Instruction Cache to Decoder
    logic [FetchWidth-1:0] ic_to_dec_valid;
    logic dec_to_ic_ready;
    ic_to_dec_data_t ic_to_dec_data;

    // Decoder to Fetcher
    logic        dec_to_fetch_decoded,            dec_to_fetch_decoded_q;
    fetch_mask_t dec_to_fetch_decoded_unused_ibe;
    logic        dec_to_fetch_stop_warp,          dec_to_fetch_stop_warp_q;
    logic        dec_to_fetch_decoded_branch,     dec_to_fetch_decoded_branch_q;
    logic        dec_to_fetch_decoded_sync,       dec_to_fetch_decoded_sync_q;
    wid_t        dec_to_fetch_decoded_warp_id,    dec_to_fetch_decoded_warp_id_q;
    subwarp_id_t dec_to_fetch_decoded_subwarp_id, dec_to_fetch_decoded_subwarp_id_q;
    pc_t         dec_to_fetch_decoded_next_pc,    dec_to_fetch_decoded_next_pc_q;

    // Decoder to Instruction Buffer
    logic dec_to_ib_valid_d, dec_to_ib_valid_q;
    logic ib_to_dec_ready_d, ib_to_dec_ready_q;
    dec_to_ib_data_t dec_to_ib_data_d, dec_to_ib_data_q;

    // Instruction Buffer to Fetcher
    fetch_mask_t [NumWarps-1:0] ib_space_available; // Which warp has space for a new instruction?
    logic        [NumWarps-1:0] ib_all_instr_finished; // Are there any instructions in flight?

    // Multi Warp Dispatcher to Register Operand Collector Stage
    logic disp_to_opc_valid, opc_to_disp_ready;
    disp_to_opc_data_t disp_to_opc_data;

    // Register Operand Collector Stage to Execution Units
    logic opc_to_eu_valid_d, opc_to_eu_valid_q,  eu_to_opc_ready_d, eu_to_opc_ready_q;
    logic opc_to_iu_valid,  iu_to_opc_ready;
    logic opc_to_fpu_valid, fpu_to_opc_ready;
    logic opc_to_lsu_valid, lsu_to_opc_ready;
    logic opc_to_bru_valid, bru_to_opc_ready;
    opc_to_eu_data_t opc_to_eu_data_q, opc_to_eu_data_d;

    // Execution Units to Register Operand Collector Stage
    logic iu_to_rc_valid,  rc_to_iu_ready;
    logic fpu_to_rc_valid, rc_to_fpu_ready;
    logic lsu_to_rc_valid, rc_to_lsu_ready;
    logic bru_to_rc_valid, rc_to_bru_ready;
    eu_to_opc_data_t iu_to_rc_data, fpu_to_rc_data, lsu_to_rc_data, bru_to_rc_data;
    
    // Writeback from Execution Units to Register Operand Collector Stage
    logic [WritebackWidth-1:0] opc_to_eu_ready_q, opc_to_eu_ready_d;
    logic [WritebackWidth-1:0] eu_to_opc_valid_q, eu_to_opc_valid_d;
    eu_to_opc_data_t [WritebackWidth-1:0] eu_to_opc_data_q,  eu_to_opc_data_d;

    iid_t       [WritebackWidth-1:0] eu_to_opc_data_tags_q;
    act_mask_t  [WritebackWidth-1:0] eu_to_opc_data_act_masks_q;
    reg_idx_t   [WritebackWidth-1:0] eu_to_opc_data_dsts_q;
    warp_data_t [WritebackWidth-1:0] eu_to_opc_data_data_q;

    // Branch Unit to Fetcher
    logic      bru_branch;
    wid_t      bru_branch_wid;
    act_mask_t bru_branching_mask;
    pc_t       bru_branch_pc;

    // Result Collector
    rc_mask_t [WritebackWidth-1:0] eu_to_rc_valid;
    rc_mask_t [WritebackWidth-1:0] rc_to_eu_ready;
    rc_mask_t rc_to_eu_ready_comb;

    // #######################################################################################
    // # Fetcher                                                                             #
    // #######################################################################################

    fetcher #(
        .FetchWidth   ( FetchWidth    ),
        .PcWidth      ( PcWidth       ),
        .NumWarps     ( NumWarps      ),
        .WarpWidth    ( WarpWidth     ),
        .AddressWidth ( AddressWidth  ),
        .TblockIdxBits( TblockIdxBits ),
        .TgroupIdBits ( TgroupIdBits  )
    ) i_fetcher (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .warp_free_o          ( warp_free_o           ),
        .allocate_warp_i      ( allocate_warp_i       ),
        .allocate_pc_i        ( allocate_pc_i         ),
        .allocate_dp_addr_i   ( allocate_dp_addr_i    ),
        .allocate_tblock_idx_i( allocate_tblock_idx_i ),
        .allocate_tgroup_id_i ( allocate_tgroup_id_i  ),

        .tblock_done_ready_i( tblock_done_ready_i ),
        .tblock_done_o      ( tblock_done_o       ),
        .tblock_done_id_o   ( tblock_done_id_o    ),

        .ib_space_available_i   ( ib_space_available    ),
        .ib_all_instr_finished_i( ib_all_instr_finished ),

        .ic_ready_i     ( ic_to_fe_ready_q           ),
        .fe_valid_o     ( fe_to_ic_valid_d           ),
        .fe_fetch_mask_o( fe_to_ic_data_d.fetch_mask ),
        .fe_pc_o        ( fe_to_ic_data_d.pc         ),
        .fe_act_mask_o  ( fe_to_ic_data_d.act_mask   ),
        .fe_warp_id_o   ( fe_to_ic_data_d.warp_id    ),
        .fe_subwarp_id_o( fe_to_ic_data_d.subwarp_id ),

        .dec_decoded_i           ( dec_to_fetch_decoded_q            ),
        .dec_stop_warp_i         ( dec_to_fetch_stop_warp_q          ),
        .dec_decoded_branch_i    ( dec_to_fetch_decoded_branch_q     ),
        .dec_decoded_sync_i      ( dec_to_fetch_decoded_sync_q       ),
        .dec_decoded_warp_id_i   ( dec_to_fetch_decoded_warp_id_q    ),
        .dec_decoded_subwarp_id_i( dec_to_fetch_decoded_subwarp_id_q ),
        .dec_decoded_next_pc_i   ( dec_to_fetch_decoded_next_pc_q    ),

        .warp_dp_addr_o   ( fe_to_iu_warp_dp_addr    ),
        .warp_tblock_idx_o( fe_to_iu_warp_tblock_idx ),

        .bru_branch_i        ( bru_branch         ),
        .bru_branch_wid_i    ( bru_branch_wid     ),
        .bru_branching_mask_i( bru_branching_mask ),
        .bru_branch_pc_i     ( bru_branch_pc      )
    );

    `FF(dec_to_fetch_decoded_q,            dec_to_fetch_decoded,            '0, clk_i, rst_ni)
    `FF(dec_to_fetch_stop_warp_q,          dec_to_fetch_stop_warp,          '0, clk_i, rst_ni)
    `FF(dec_to_fetch_decoded_branch_q,     dec_to_fetch_decoded_branch,     '0, clk_i, rst_ni)
    `FF(dec_to_fetch_decoded_sync_q,       dec_to_fetch_decoded_sync,       '0, clk_i, rst_ni)
    `FF(dec_to_fetch_decoded_warp_id_q,    dec_to_fetch_decoded_warp_id,    '0, clk_i, rst_ni)
    `FF(dec_to_fetch_decoded_next_pc_q,    dec_to_fetch_decoded_next_pc,    '0, clk_i, rst_ni)
    `FF(dec_to_fetch_decoded_subwarp_id_q, dec_to_fetch_decoded_subwarp_id, '0, clk_i, rst_ni)

    // #######################################################################################
    // # Fetcher to Instruction Cache - Register                                             #
    // #######################################################################################

    stream_register #(
        .T( fe_to_ic_data_t )
    ) i_fe_to_ic_reg (
        .clk_i     ( clk_i      ),
        .rst_ni    ( rst_ni     ),
        .clr_i     ( 1'b0       ),
        .testmode_i( testmode_i ),

        .valid_i( fe_to_ic_valid_d ),
        .ready_o( ic_to_fe_ready_q ),
        .data_i ( fe_to_ic_data_d  ),

        .valid_o( fe_to_ic_valid_q ),
        .ready_i( ic_to_fe_ready_d ),
        .data_o ( fe_to_ic_data_q  )
    );

    // #######################################################################################
    // # Instruction Cache                                                                   #
    // #######################################################################################

    instruction_cache #(
        .FetchWidth      ( FetchWidth    ),
        .PcWidth         ( PcWidth       ),
        .NumWarps        ( NumWarps      ),
        .WarpWidth       ( WarpWidth     ),
        .EncInstWidth    ( EncInstWidth  ),
        .CachelineIdxBits( IClineIdxBits ),
        .NumCachelines   ( NumIClines    )
    ) i_instruction_cache (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .mem_ready_i( imem_ready_i     ),
        .mem_req_o  ( imem_req_valid_o ),
        .mem_addr_o ( imem_req_addr_o  ),

        .mem_valid_i( imem_rsp_valid_i ),
        .mem_data_i ( imem_rsp_data_i  ),

        .flush_i ( flush_ic_i ),

        .ic_ready_o     ( ic_to_fe_ready_d           ),
        .fe_valid_i     ( fe_to_ic_valid_q           ),
        .fe_fetch_mask_i( fe_to_ic_data_q.fetch_mask ),
        .fe_pc_i        ( fe_to_ic_data_q.pc         ),
        .fe_act_mask_i  ( fe_to_ic_data_q.act_mask   ),
        .fe_warp_id_i   ( fe_to_ic_data_q.warp_id    ),
        .fe_subwarp_id_i( fe_to_ic_data_q.subwarp_id ),

        .dec_ready_i    ( dec_to_ic_ready           ),
        .ic_valid_o     ( ic_to_dec_valid           ),
        .ic_fetch_mask_o( ic_to_dec_data.fetch_mask ),
        .ic_pc_o        ( ic_to_dec_data.pc         ),
        .ic_act_mask_o  ( ic_to_dec_data.act_mask   ),
        .ic_warp_id_o   ( ic_to_dec_data.warp_id    ),
        .ic_inst_o      ( ic_to_dec_data.inst       ),
        .ic_subwarp_id_o( ic_to_dec_data.subwarp_id )
    );

    // #######################################################################################
    // # Instruction Decoder                                                                 #
    // #######################################################################################

    decoder #(
        .FetchWidth     ( FetchWidth      ),
        .PcWidth        ( PcWidth         ),
        .NumWarps       ( NumWarps        ),
        .WarpWidth      ( WarpWidth       ),
        .EncInstWidth   ( EncInstWidth    ),
        .RegIdxWidth    ( RegIdxWidth     ),
        .OperandsPerInst( OperandsPerInst )
    ) i_decoder (
        .dec_ready_o    ( dec_to_ic_ready           ),
        .ic_valid_i     ( ic_to_dec_valid           ),
        .ic_fetch_mask_i( ic_to_dec_data.fetch_mask ),
        .ic_pc_i        ( ic_to_dec_data.pc         ),
        .ic_act_mask_i  ( ic_to_dec_data.act_mask   ),
        .ic_warp_id_i   ( ic_to_dec_data.warp_id    ),
        .ic_subwarp_id_i( ic_to_dec_data.subwarp_id ),
        .ic_inst_i      ( ic_to_dec_data.inst       ),

        .disp_ready_i         ( ib_to_dec_ready_q                ),
        .dec_valid_o          ( dec_to_ib_data_d.valid_insts     ),
        .dec_pc_o             ( dec_to_ib_data_d.pc              ),
        .dec_act_mask_o       ( dec_to_ib_data_d.act_mask        ),
        .dec_warp_id_o        ( dec_to_ib_data_d.warp_id         ),
        .dec_subwarp_id_o     ( dec_to_ib_data_d.subwarp_id      ),
        .dec_inst_o           ( dec_to_ib_data_d.inst            ),
        .dec_dst_o            ( dec_to_ib_data_d.dst             ),
        .dec_operands_is_reg_o( dec_to_ib_data_d.operands_is_reg ),
        .dec_operands_o       ( dec_to_ib_data_d.operands        ),

        .dec_decoded_o           ( dec_to_fetch_decoded            ),
        .dec_decoded_unused_ibe_o( dec_to_fetch_decoded_unused_ibe ),
        .dec_stop_warp_o         ( dec_to_fetch_stop_warp          ),
        .dec_decoded_branch_o    ( dec_to_fetch_decoded_branch     ),
        .dec_decoded_sync_o      ( dec_to_fetch_decoded_sync       ),
        .dec_decoded_warp_id_o   ( dec_to_fetch_decoded_warp_id    ),
        .dec_decoded_subwarp_id_o( dec_to_fetch_decoded_subwarp_id ),
        .dec_decoded_next_pc_o   ( dec_to_fetch_decoded_next_pc    )
    );

    // #######################################################################################
    // # Decoder to Instruction Buffer - Register                                            #
    // #######################################################################################

    assign dec_to_ib_valid_d = |dec_to_ib_data_d.valid_insts;

    stream_register #(
        .T( dec_to_ib_data_t )
    ) i_dec_to_ib_reg (
        .clk_i     ( clk_i      ),
        .rst_ni    ( rst_ni     ),
        .clr_i     ( 1'b0       ),
        .testmode_i( testmode_i ),

        .valid_i( dec_to_ib_valid_d ),
        .ready_o( ib_to_dec_ready_q ),
        .data_i ( dec_to_ib_data_d  ),

        .valid_o( dec_to_ib_valid_q ),
        .ready_i( ib_to_dec_ready_d ),
        .data_o ( dec_to_ib_data_q  )
    );

    // #######################################################################################
    // # Multi Warp Dispatcher                                                               #
    // #######################################################################################

    multi_warp_dispatcher #(
        .WritebackWidth       ( WritebackWidth       ),
        .FetchWidth           ( FetchWidth           ),
        .NumTags              ( NumTags              ),
        .PcWidth              ( PcWidth              ),
        .NumWarps             ( NumWarps             ),
        .WarpWidth            ( WarpWidth            ),
        .WaitBufferSizePerWarp( InflightInstrPerWarp ),
        .RegIdxWidth          ( RegIdxWidth          ),
        .OperandsPerInst      ( OperandsPerInst      )
    ) i_warp_dispatcher (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .inorder_execution_i( inorder_execution_i ),

        .fe_handshake_i( fe_to_ic_valid_d && ic_to_fe_ready_q ),
        .fe_warp_id_i  ( fe_to_ic_data_d.warp_id              ),

        .ib_space_available_o   ( ib_space_available    ),
        .ib_all_instr_finished_o( ib_all_instr_finished ),

        .dec_decoded_i           ( dec_to_fetch_decoded            ),
        .dec_decoded_unused_ibe_i( dec_to_fetch_decoded_unused_ibe ),
        .dec_decoded_warp_id_i   ( dec_to_fetch_decoded_warp_id    ),

        .ib_ready_o            ( ib_to_dec_ready_d                ),
        .dec_valid_i           ( dec_to_ib_valid_q                ),
        .dec_pc_i              ( dec_to_ib_data_q.pc              ),
        .dec_act_mask_i        ( dec_to_ib_data_q.act_mask        ),
        .dec_warp_id_i         ( dec_to_ib_data_q.warp_id         ),
        .dec_subwarp_id_i      ( dec_to_ib_data_q.subwarp_id      ),
        .dec_valid_insts_i     ( dec_to_ib_data_q.valid_insts     ),
        .dec_inst_i            ( dec_to_ib_data_q.inst            ),
        .dec_dst_i             ( dec_to_ib_data_q.dst             ),
        .dec_operands_is_reg_i ( dec_to_ib_data_q.operands_is_reg ),
        .dec_operands_i        ( dec_to_ib_data_q.operands        ),

        .opc_ready_i           ( opc_to_disp_ready                ),
        .disp_valid_o          ( disp_to_opc_valid                ),
        .disp_tag_o            ( disp_to_opc_data.tag             ),
        .disp_pc_o             ( disp_to_opc_data.pc              ),
        .disp_act_mask_o       ( disp_to_opc_data.act_mask        ),
        .disp_inst_o           ( disp_to_opc_data.inst            ),
        .disp_dst_o            ( disp_to_opc_data.dst             ),
        .disp_operands_is_reg_o( disp_to_opc_data.operands_is_reg ),
        .disp_operands_o       ( disp_to_opc_data.operands        ),

        .opc_eu_handshake_i( opc_to_eu_valid_d && eu_to_opc_ready_q ),
        .opc_eu_tag_i      ( opc_to_eu_data_d.tag                   ),

        .eu_valid_i( eu_to_opc_valid_q & opc_to_eu_ready_d ),
        .eu_tag_i  ( eu_to_opc_data_tags_q                 )
    );

    // #######################################################################################
    // # Register Operand Collector Stage                                                    #
    // #######################################################################################

    register_opc_stage #(
        .WritebackWidth       ( WritebackWidth        ),
        .NumTags              ( NumTags               ),
        .PcWidth              ( PcWidth               ),
        .NumWarps             ( NumWarps              ),
        .WarpWidth            ( WarpWidth             ),
        .RegIdxWidth          ( RegIdxWidth           ),
        .OperandsPerInst      ( OperandsPerInst       ),
        .NumBanks             ( NumBanks              ),
        .RegWidth             ( RegWidth              ),
        .DualPortRegisterBanks( DualPortRegisterBanks ),
        .NumOperandCollectors ( NumOperandCollectors  )
    ) i_register_opc_stage (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .opc_ready_o        ( opc_to_disp_ready                ),
        .disp_valid_i       ( disp_to_opc_valid                ),
        .disp_tag_i         ( disp_to_opc_data.tag             ),
        .disp_pc_i          ( disp_to_opc_data.pc              ),
        .disp_act_mask_i    ( disp_to_opc_data.act_mask        ),
        .disp_inst_i        ( disp_to_opc_data.inst            ),
        .disp_dst_i         ( disp_to_opc_data.dst             ),
        .disp_src_required_i( disp_to_opc_data.operands_is_reg ),
        .disp_src_i         ( disp_to_opc_data.operands        ),

        .eu_ready_i        ( eu_to_opc_ready_q         ),
        .opc_valid_o       ( opc_to_eu_valid_d         ),
        .opc_tag_o         ( opc_to_eu_data_d.tag      ),
        .opc_pc_o          ( opc_to_eu_data_d.pc       ),
        .opc_act_mask_o    ( opc_to_eu_data_d.act_mask ),
        .opc_inst_o        ( opc_to_eu_data_d.inst     ),
        .opc_dst_o         ( opc_to_eu_data_d.dst      ),
        .opc_operand_data_o( opc_to_eu_data_d.operands ),

        .opc_to_eu_ready_o( opc_to_eu_ready_d          ),
        .eu_valid_i       ( eu_to_opc_valid_q          ),
        .eu_act_mask_i    ( eu_to_opc_data_act_masks_q ),
        .eu_tag_i         ( eu_to_opc_data_tags_q      ),
        .eu_dst_i         ( eu_to_opc_data_dsts_q      ),
        .eu_data_i        ( eu_to_opc_data_data_q      )
    );

    // #######################################################################################
    // # Execution Unit Demux                                                                #
    // #######################################################################################

    spill_register #(
        .T( opc_to_eu_data_t )
    ) i_opc_to_eu_reg (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .valid_i( opc_to_eu_valid_d ),
        .ready_o( eu_to_opc_ready_q ),
        .data_i ( opc_to_eu_data_d  ),

        .valid_o( opc_to_eu_valid_q ),
        .ready_i( eu_to_opc_ready_d ),
        .data_o ( opc_to_eu_data_q  )
    );

    stream_demux #(
        .N_OUP(4)
    ) i_eu_demux (
        .inp_valid_i( opc_to_eu_valid_q ),
        .inp_ready_o( eu_to_opc_ready_d ),

        .oup_sel_i( opc_to_eu_data_q.inst.eu ),

        .oup_valid_o({ opc_to_fpu_valid, opc_to_bru_valid, opc_to_lsu_valid, opc_to_iu_valid }),
        .oup_ready_i({ fpu_to_opc_ready, bru_to_opc_ready, lsu_to_opc_ready, iu_to_opc_ready })
    );

    `ifndef SYNTHESIS
        assert property (@(posedge clk_i) opc_to_eu_valid_q
            |-> opc_to_eu_data_q.inst.eu inside {EU_IU, EU_LSU, EU_BRU, EU_FPU})
            else $error("Invalid execution unit type: %0d", opc_to_eu_data_q.inst.eu);
    `endif

    // #######################################################################################
    // # Execution Units                                                                     #
    // #######################################################################################

    // Integer Unit
    integer_unit #(
        .NumTags        ( NumTags         ),
        .NumWarps       ( NumWarps        ),
        .RegWidth       ( RegWidth        ),
        .WarpWidth      ( WarpWidth       ),
        .OperandsPerInst( OperandsPerInst ),
        .RegIdxWidth    ( RegIdxWidth     ),
        .AddressWidth   ( AddressWidth    ),
        .TblockIdxBits  ( TblockIdxBits   )
    ) i_integer_unit (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .testmode_i( testmode_i ),

        .fe_to_iu_warp_dp_addr_i   ( fe_to_iu_warp_dp_addr    ),
        .fe_to_iu_warp_tblock_idx_i( fe_to_iu_warp_tblock_idx ),

        .eu_to_opc_ready_o   ( iu_to_opc_ready                  ),
        .opc_to_eu_valid_i   ( opc_to_iu_valid                  ),
        .opc_to_eu_act_mask_i( opc_to_eu_data_q.act_mask        ),
        .opc_to_eu_tag_i     ( opc_to_eu_data_q.tag             ),
        .opc_to_eu_inst_sub_i( opc_to_eu_data_q.inst.subtype.iu ),
        .opc_to_eu_dst_i     ( opc_to_eu_data_q.dst             ),
        .opc_to_eu_operands_i( opc_to_eu_data_q.operands        ),

        .rc_to_eu_ready_i   ( rc_to_iu_ready         ),
        .eu_to_rc_valid_o   ( iu_to_rc_valid         ),
        .eu_to_rc_act_mask_o( iu_to_rc_data.act_mask ),
        .eu_to_rc_tag_o     ( iu_to_rc_data.tag      ),
        .eu_to_rc_dst_o     ( iu_to_rc_data.dst      ),
        .eu_to_rc_data_o    ( iu_to_rc_data.data     )
    );

    // Floating Point Unit
    floating_point_unit #(
        .NumTags        ( NumTags         ),
        .NumWarps       ( NumWarps        ),
        .RegWidth       ( RegWidth        ),
        .WarpWidth      ( WarpWidth       ),
        .OperandsPerInst( OperandsPerInst ),
        .RegIdxWidth    ( RegIdxWidth     ),
        .AddressWidth   ( AddressWidth    ),
        .TblockIdxBits  ( TblockIdxBits   )
    ) i_floating_point_unit (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .testmode_i( testmode_i ),

        .eu_to_opc_ready_o   ( fpu_to_opc_ready                  ),
        .opc_to_eu_valid_i   ( opc_to_fpu_valid                  ),
        .opc_to_eu_act_mask_i( opc_to_eu_data_q.act_mask         ),
        .opc_to_eu_tag_i     ( opc_to_eu_data_q.tag              ),
        .opc_to_eu_inst_sub_i( opc_to_eu_data_q.inst.subtype.fpu ),
        .opc_to_eu_dst_i     ( opc_to_eu_data_q.dst              ),
        .opc_to_eu_operands_i( opc_to_eu_data_q.operands         ),

        .rc_to_eu_ready_i   ( rc_to_fpu_ready         ),
        .eu_to_rc_valid_o   ( fpu_to_rc_valid         ),
        .eu_to_rc_act_mask_o( fpu_to_rc_data.act_mask ),
        .eu_to_rc_tag_o     ( fpu_to_rc_data.tag      ),
        .eu_to_rc_dst_o     ( fpu_to_rc_data.dst      ),
        .eu_to_rc_data_o    ( fpu_to_rc_data.data     )
    );

    // Load Store Unit
    load_store_unit #(
        .RegWidth              ( RegWidth               ),
        .WarpWidth             ( WarpWidth              ),
        .OperandsPerInst       ( OperandsPerInst        ),
        .RegIdxWidth           ( RegIdxWidth            ),
        .iid_t                 ( iid_t                  ),
        .AddressWidth          ( AddressWidth           ),
        .BlockIdxBits          ( BlockIdxBits           ),
        .OutstandingReqIdxWidth( OutstandingReqIdxWidth )
    ) i_load_store_unit (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .testmode_i( testmode_i ),

        .eu_to_opc_ready_o   ( lsu_to_opc_ready                  ),
        .opc_to_eu_valid_i   ( opc_to_lsu_valid                  ),
        .opc_to_eu_tag_i     ( opc_to_eu_data_q.tag              ),
        .opc_to_eu_inst_sub_i( opc_to_eu_data_q.inst.subtype.lsu ),
        .opc_to_eu_act_mask_i( opc_to_eu_data_q.act_mask         ),
        .opc_to_eu_dst_i     ( opc_to_eu_data_q.dst              ),
        .opc_to_eu_operands_i( opc_to_eu_data_q.operands         ),

        .rc_to_eu_ready_i   ( rc_to_lsu_ready         ),
        .eu_to_rc_valid_o   ( lsu_to_rc_valid         ),
        .eu_to_rc_act_mask_o( lsu_to_rc_data.act_mask ),
        .eu_to_rc_tag_o     ( lsu_to_rc_data.tag      ),
        .eu_to_rc_dst_o     ( lsu_to_rc_data.dst      ),
        .eu_to_rc_data_o    ( lsu_to_rc_data.data     ),

        .mem_ready_i      ( mem_ready_i       ),
        .mem_req_valid_o  ( mem_req_valid_o   ),
        .mem_req_id_o     ( mem_req_id_o      ),
        .mem_req_addr_o   ( mem_req_addr_o    ),
        .mem_req_we_mask_o( mem_req_we_mask_o ),
        .mem_req_wdata_o  ( mem_req_wdata_o   ),

        .mem_rsp_valid_i  ( mem_rsp_valid_i   ),
        .mem_rsp_id_i     ( mem_rsp_id_i      ),
        .mem_rsp_data_i   ( mem_rsp_data_i    )
    );

    // Branch Unit
    branch_unit #(
        .NumTags        ( NumTags         ),
        .NumWarps       ( NumWarps        ),
        .RegWidth       ( RegWidth        ),
        .WarpWidth      ( WarpWidth       ),
        .OperandsPerInst( OperandsPerInst ),
        .RegIdxWidth    ( RegIdxWidth     ),
        .AddressWidth   ( AddressWidth    ),
        .PcWidth        ( PcWidth         )
    ) i_branch_unit (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .testmode_i( testmode_i ),

        .eu_to_opc_ready_o   ( bru_to_opc_ready                  ),
        .opc_to_eu_valid_i   ( opc_to_bru_valid                  ),
        .opc_to_eu_act_mask_i( opc_to_eu_data_q.act_mask         ),
        .opc_to_eu_tag_i     ( opc_to_eu_data_q.tag              ),
        .opc_to_eu_pc_i      ( opc_to_eu_data_q.pc               ),
        .opc_to_eu_inst_sub_i( opc_to_eu_data_q.inst.subtype.bru ),
        .opc_to_eu_dst_i     ( opc_to_eu_data_q.dst              ),
        .opc_to_eu_operands_i( opc_to_eu_data_q.operands         ),

        .rc_to_eu_ready_i   ( rc_to_bru_ready         ),
        .eu_to_rc_valid_o   ( bru_to_rc_valid         ),
        .eu_to_rc_act_mask_o( bru_to_rc_data.act_mask ),
        .eu_to_rc_tag_o     ( bru_to_rc_data.tag      ),
        .eu_to_rc_dst_o     ( bru_to_rc_data.dst      ),
        .eu_to_rc_data_o    ( bru_to_rc_data.data     ),

        .bru_branch_o        ( bru_branch         ),
        .bru_branch_wid_o    ( bru_branch_wid     ),
        .bru_branching_mask_o( bru_branching_mask ),
        .bru_branch_pc_o     ( bru_branch_pc      )
    );

    // #######################################################################################
    // # Execution Unit Result Collector                                                     #
    // #######################################################################################

    // Combine ready signals from all writeback ports
    always_comb begin : combine_rc_ready_signals
        rc_to_eu_ready_comb = '0;
        for (int wb = 0; wb < WritebackWidth; wb++) begin
            rc_to_eu_ready_comb = rc_to_eu_ready_comb | rc_to_eu_ready[wb];
        end
    end : combine_rc_ready_signals

    // Extract ready signals for each execution unit
    assign rc_to_bru_ready = rc_to_eu_ready_comb[0];
    assign rc_to_lsu_ready = rc_to_eu_ready_comb[1];
    assign rc_to_iu_ready  = rc_to_eu_ready_comb[2];
    assign rc_to_fpu_ready = rc_to_eu_ready_comb[3];

    // Generate writeback ports
    for (genvar wb = 0; wb < WritebackWidth; wb++) begin : gen_writeback
        // Valid signals
        // Port 0: take directly from EUs
        // Port N: only valid if previous port was not ready
        if (wb == 0)
            assign eu_to_rc_valid[wb] = {fpu_to_rc_valid, iu_to_rc_valid, lsu_to_rc_valid, bru_to_rc_valid};
        else
            assign eu_to_rc_valid[wb] = eu_to_rc_valid[wb-1] & (~rc_to_eu_ready[wb-1]);

        stream_arbiter #(
            .DATA_T ( eu_to_opc_data_t ),
            .N_INP  ( 4                ),
            .ARBITER( "prio"           )
        ) i_result_collector (
            .clk_i ( clk_i  ),
            .rst_ni( rst_ni ),

            .inp_data_i ({ fpu_to_rc_data, iu_to_rc_data, lsu_to_rc_data, bru_to_rc_data }),
            .inp_valid_i( eu_to_rc_valid[wb] ),
            .inp_ready_o( rc_to_eu_ready[wb] ),

            .oup_data_o ( eu_to_opc_data_d [wb] ),
            .oup_valid_o( eu_to_opc_valid_d[wb] ),
            .oup_ready_i( opc_to_eu_ready_q[wb] )
        );

        stream_register #(
            .T( eu_to_opc_data_t )
        ) i_eu_to_opc_reg (
            .clk_i     ( clk_i      ),
            .rst_ni    ( rst_ni     ),
            .clr_i     ( 1'b0       ),
            .testmode_i( testmode_i ),

            .valid_i( eu_to_opc_valid_d[wb] ),
            .ready_o( opc_to_eu_ready_q[wb] ),
            .data_i ( eu_to_opc_data_d [wb] ),

            .valid_o( eu_to_opc_valid_q[wb] ),
            .ready_i( opc_to_eu_ready_d[wb] ),
            .data_o ( eu_to_opc_data_q [wb] )
        );

        assign eu_to_opc_data_tags_q     [wb] = eu_to_opc_data_q[wb].tag;
        assign eu_to_opc_data_act_masks_q[wb] = eu_to_opc_data_q[wb].act_mask;
        assign eu_to_opc_data_dsts_q     [wb] = eu_to_opc_data_q[wb].dst;
        assign eu_to_opc_data_data_q     [wb] = eu_to_opc_data_q[wb].data;
    end : gen_writeback

`ifndef SYNTHESIS
    initial begin : disp_dumper
        integer f;
        string data, filename;

        filename = $sformatf("disp_cc%0d_cu%0d.log", ClusterId, ComputeUnitId);
        f = $fopen(filename, "w");

        while (1) begin
            @(posedge clk_i);
            if (disp_to_opc_valid && opc_to_disp_ready) begin
                data = $sformatf("%t: Tag: %0d, Pc: %0x, Inst: %0d, Warp: %0d, AM: %b, Dst: r%0d,",
                    $time(), disp_to_opc_data.tag, disp_to_opc_data.pc, disp_to_opc_data.inst,
                    disp_to_opc_data.tag[WidWidth-1:0], disp_to_opc_data.act_mask,
                    disp_to_opc_data.dst);

                data = {data, $sformatf(" OpIsReg: %b", disp_to_opc_data.operands_is_reg)};

                for (int i = 0; i < OperandsPerInst; i++) begin
                    data = {data, $sformatf(", Operand%0d: %0d", i, disp_to_opc_data.operands[i])};
                end
                $fwrite(f, "%s\n", data);
                $fflush(f);
            end
        end
    end : disp_dumper

    initial begin : iu_dumper
        integer f;
        string data, filename;

        filename = $sformatf("iu_cc%0d_cu%0d.log", ClusterId, ComputeUnitId);
        f = $fopen(filename, "w");

        while (1) begin
            @(posedge clk_i);
            if (opc_to_iu_valid && iu_to_opc_ready) begin
                data = $sformatf("%t: Tag: %0d, Subtype: %0d, Warp: %0d, ActMask: %b, Dst: r%0d",
                    $time(), opc_to_eu_data_q.tag, opc_to_eu_data_q.inst.subtype,
                    opc_to_eu_data_q.tag[WidWidth-1:0], opc_to_eu_data_q.act_mask,
                    opc_to_eu_data_q.dst);

                for (int i = 0; i < OperandsPerInst; i++) begin
                    data = {data, $sformatf(", Operand%0d:", i)};
                    for (int thread = 0; thread < WarpWidth; thread++) begin
                        data = {data, $sformatf(" (t%0d: 0x%h)", thread,
                            opc_to_eu_data_q.operands[i][thread * RegWidth +: RegWidth])};
                    end
                end
                $fwrite(f, "%s\n", data);
                $fflush(f);
            end
        end
    end : iu_dumper

    initial begin : fpu_dumper
        integer f;
        string data, filename;

        filename = $sformatf("fpu_cc%0d_cu%0d.log", ClusterId, ComputeUnitId);
        f = $fopen(filename, "w");

        while (1) begin
            @(posedge clk_i);
            if (opc_to_fpu_valid && fpu_to_opc_ready) begin
                data = $sformatf("%t: Tag: %0d, Subtype: %0d, Warp: %0d, ActMask: %b, Dst: r%0d",
                    $time(), opc_to_eu_data_q.tag, opc_to_eu_data_q.inst.subtype,
                    opc_to_eu_data_q.tag[WidWidth-1:0], opc_to_eu_data_q.act_mask,
                    opc_to_eu_data_q.dst);

                for (int i = 0; i < OperandsPerInst; i++) begin
                    data = {data, $sformatf(", Operand%0d:", i)};
                    for (int thread = 0; thread < WarpWidth; thread++) begin
                        data = {data, $sformatf(" (t%0d: 0x%h)", thread,
                            opc_to_eu_data_q.operands[i][thread * RegWidth +: RegWidth])};
                    end
                end
                $fwrite(f, "%s\n", data);
                $fflush(f);
            end
        end
    end : fpu_dumper

    initial begin : lsu_dumper
        integer f;
        string data, filename;

        filename = $sformatf("lsu_cc%0d_cu%0d.log", ClusterId, ComputeUnitId);
        f = $fopen(filename, "w");

        while (1) begin
            @(posedge clk_i);
            if (opc_to_lsu_valid && lsu_to_opc_ready) begin
                data = $sformatf("%t: Tag: %0d, Subtype: %0d, Warp: %0d, ActMask: %b, Dst: r%0d",
                    $time(), opc_to_eu_data_q.tag, opc_to_eu_data_q.inst.subtype,
                    opc_to_eu_data_q.tag[WidWidth-1:0], opc_to_eu_data_q.act_mask,
                    opc_to_eu_data_q.dst);

                for (int i = 0; i < OperandsPerInst; i++) begin
                    data = {data, $sformatf(", Operand%0d:", i)};
                    for (int thread = 0; thread < WarpWidth; thread++) begin
                        data = {data, $sformatf(" (t%0d: 0x%h)", thread,
                            opc_to_eu_data_q.operands[i][thread * RegWidth +: RegWidth])};
                    end
                end
                $fwrite(f, "%s\n", data);
                $fflush(f);
            end
        end
    end : lsu_dumper

    initial begin : result_dumper
        integer f;
        string data, filename;

        filename = $sformatf("results_cc%0d_cu%0d.log", ClusterId, ComputeUnitId);
        f = $fopen(filename, "w");

        while (1) begin
            @(posedge clk_i);
            for (int wb = 0; wb < WritebackWidth; wb++) begin : loop_writeback_ports
                if (eu_to_opc_valid_q[wb] && opc_to_eu_ready_d[wb]) begin
                    data = $sformatf("%t: Tag: %0d, Warp: %0d, ActMask: %b, Dst: r%0d, Data: ", $time(),
                        eu_to_opc_data_q[wb].tag, eu_to_opc_data_q[wb].tag[WidWidth-1:0],
                        eu_to_opc_data_q[wb].act_mask, eu_to_opc_data_q[wb].dst);

                    for (int thread = 0; thread < WarpWidth; thread++) begin
                        data = {data, $sformatf(" (t%0d: 0x%h)", thread,
                            eu_to_opc_data_q[wb].data[thread * RegWidth +: RegWidth])};
                    end
                    $fwrite(f, "%s\n", data);
                    $fflush(f);
                end
            end : loop_writeback_ports
        end
    end : result_dumper
`endif
endmodule : compute_unit
