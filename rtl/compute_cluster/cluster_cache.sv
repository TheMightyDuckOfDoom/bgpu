// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "hpdcache_typedef.svh"

/// Compute Cluster Cache
// Multiple HPD Caches that are shared between multiple compute units
module cluster_cache import hpdcache_pkg::*; #(
    // Memory Address width in bits
    parameter int unsigned AddressWidth = 32,
    // Memory Block index width -> Memory request width is 2^BlockIdxBits bytes
    // Must be greater or equal to 2
    parameter int unsigned BlockIdxBits = 4,

    // Width of the Memory system bus in bits
    // Must be a multiple of 32
    parameter int unsigned MemoryWidth = 512,

    // Number of ways
    parameter int unsigned NumWays = 8,

    // Number of sets
    parameter int unsigned NumSets = 64,

    parameter int unsigned MshrSets = 32,
    parameter int unsigned MshrWays = 2,

    /// Dependent parameter, do **not** overwrite.
    parameter int unsigned WordWidth = 32,
    parameter int unsigned RequestWords = (1 << BlockIdxBits) / (WordWidth / 8),

  parameter int unsigned HPDCACHE_NREQUESTERS = 1,

  parameter hpdcache_pkg::hpdcache_user_cfg_t HPDcacheUserCfg = '{
      nRequesters: HPDCACHE_NREQUESTERS,
      paWidth:     AddressWidth,
      wordWidth:   WordWidth,

      sets: NumSets,
      ways: NumWays,

      clWords:  MemoryWidth / WordWidth, // Cacheline Size
      reqWords: RequestWords,            // Words per request

      reqTransIdWidth: 6, // Dont know
      reqSrcIdWidth:   3, // Dont know

      victimSel: hpdcache_pkg::HPDCACHE_VICTIM_RANDOM,

      dataRamByteEnable:  1'b1,         // Use Byte Enables
      dataWaysPerRamWord: 1,            // Store each way in it's own memory
      dataSetsPerRam:     NumSets,      // Store entire way in a single memory
      accessWords:        RequestWords, // Always access full cache line from memory

      mshrSets:           MshrSets,
      mshrWays:           MshrWays,
      mshrSetsPerRam:     MshrSets,
      mshrWaysPerRamWord: MshrWays,
      mshrRamByteEnable:  1'b1,
      mshrUseRegbank:     1,

      cbufEntries:              4,
      refillCoreRspFeedthrough: 1'b1,
      refillFifoDepth:          2,

      wbufDirEntries:   16,
      wbufDataEntries:  8,
      wbufWords:        4,
      wbufTimecntWidth: 3,

      rtabEntries:    4,
      flushEntries:   4,
      flushFifoDepth: 2,

      memAddrWidth: AddressWidth,
      memIdWidth:   7,
      memDataWidth: MemoryWidth,

      wtEn:       1'b1,
      wbEn:       1'b0,
      lowLatency: 1'b0
  },

  parameter hpdcache_pkg::hpdcache_cfg_t HPDcacheCfg = hpdcache_pkg::hpdcacheBuildConfig(
      HPDcacheUserCfg
  ),

  parameter type hpdcache_mem_addr_t = logic [HPDcacheCfg.u.memAddrWidth-1:0],
  parameter type hpdcache_mem_id_t = logic [HPDcacheCfg.u.memIdWidth-1:0],
  parameter type hpdcache_mem_data_t = logic [HPDcacheCfg.u.memDataWidth-1:0],
  parameter type hpdcache_mem_be_t = logic [HPDcacheCfg.u.memDataWidth/8-1:0],
  parameter type hpdcache_mem_req_t =
      `HPDCACHE_DECL_MEM_REQ_T(hpdcache_mem_addr_t, hpdcache_mem_id_t),
  parameter type hpdcache_mem_resp_r_t =
      `HPDCACHE_DECL_MEM_RESP_R_T(hpdcache_mem_id_t, hpdcache_mem_data_t),
  parameter type hpdcache_mem_req_w_t =
      `HPDCACHE_DECL_MEM_REQ_W_T(hpdcache_mem_data_t, hpdcache_mem_be_t),
  parameter type hpdcache_mem_resp_w_t =
      `HPDCACHE_DECL_MEM_RESP_W_T(hpdcache_mem_id_t),

  parameter type hpdcache_tag_t = logic [HPDcacheCfg.tagWidth-1:0],
  parameter type hpdcache_data_word_t = logic [HPDcacheCfg.u.wordWidth-1:0],
  parameter type hpdcache_data_be_t = logic [HPDcacheCfg.u.wordWidth/8-1:0],
  parameter type hpdcache_req_offset_t = logic [HPDcacheCfg.reqOffsetWidth-1:0],
  parameter type hpdcache_req_data_t = hpdcache_data_word_t [HPDcacheCfg.u.reqWords-1:0],
  parameter type hpdcache_req_be_t = hpdcache_data_be_t [HPDcacheCfg.u.reqWords-1:0],
  parameter type hpdcache_req_sid_t = logic [HPDcacheCfg.u.reqSrcIdWidth-1:0],
  parameter type hpdcache_req_tid_t = logic [HPDcacheCfg.u.reqTransIdWidth-1:0],
  parameter type hpdcache_req_t =
      `HPDCACHE_DECL_REQ_T(hpdcache_req_offset_t,
                           hpdcache_req_data_t,
                           hpdcache_req_be_t,
                           hpdcache_req_sid_t,
                           hpdcache_req_tid_t,
                           hpdcache_tag_t),
  parameter type hpdcache_rsp_t =
      `HPDCACHE_DECL_RSP_T(hpdcache_req_data_t,
                           hpdcache_req_sid_t,
                           hpdcache_req_tid_t),

  parameter type hpdcache_wbuf_timecnt_t = logic [HPDcacheCfg.u.wbufTimecntWidth-1:0]
)

(
  input  logic                        clk_i,
  input  logic                        rst_ni,

  input  logic                        wbuf_flush_i,
  output logic                        wbuf_empty_o,

  input  logic                        core_req_valid_i         [HPDCACHE_NREQUESTERS],
  output logic                        core_req_ready_o         [HPDCACHE_NREQUESTERS],
  input  hpdcache_req_t               core_req_i               [HPDCACHE_NREQUESTERS],
  input  logic                        core_req_abort_i         [HPDCACHE_NREQUESTERS],
  input  hpdcache_tag_t               core_req_tag_i           [HPDCACHE_NREQUESTERS],
  input  hpdcache_pkg::hpdcache_pma_t core_req_pma_i           [HPDCACHE_NREQUESTERS],
  output logic                        core_rsp_valid_o         [HPDCACHE_NREQUESTERS],
  output hpdcache_rsp_t               core_rsp_o               [HPDCACHE_NREQUESTERS],

  input  logic                        mem_req_read_ready_i,
  output logic                        mem_req_read_valid_o,
  output hpdcache_mem_req_t           mem_req_read_o,

  output logic                        mem_resp_read_ready_o,
  input  logic                        mem_resp_read_valid_i,
  input  hpdcache_mem_resp_r_t        mem_resp_read_i,

  input  logic                        mem_req_write_ready_i,
  output logic                        mem_req_write_valid_o,
  output hpdcache_mem_req_t           mem_req_write_o,

  input  logic                        mem_req_write_data_ready_i,
  output logic                        mem_req_write_data_valid_o,
  output hpdcache_mem_req_w_t         mem_req_write_data_o,

  output logic                        mem_resp_write_ready_o,
  input  logic                        mem_resp_write_valid_i,
  input  hpdcache_mem_resp_w_t        mem_resp_write_i
);

  hpdcache #(
      .HPDcacheCfg          ( HPDcacheCfg            ),
      .wbuf_timecnt_t       ( hpdcache_wbuf_timecnt_t),
      .hpdcache_tag_t       ( hpdcache_tag_t         ),
      .hpdcache_data_word_t ( hpdcache_data_word_t   ),
      .hpdcache_data_be_t   ( hpdcache_data_be_t     ),
      .hpdcache_req_offset_t( hpdcache_req_offset_t  ),
      .hpdcache_req_data_t  ( hpdcache_req_data_t    ),
      .hpdcache_req_be_t    ( hpdcache_req_be_t      ),
      .hpdcache_req_sid_t   ( hpdcache_req_sid_t     ),
      .hpdcache_req_tid_t   ( hpdcache_req_tid_t     ),
      .hpdcache_req_t       ( hpdcache_req_t         ),
      .hpdcache_rsp_t       ( hpdcache_rsp_t         ),
      .hpdcache_mem_addr_t  ( hpdcache_mem_addr_t    ),
      .hpdcache_mem_id_t    ( hpdcache_mem_id_t      ),
      .hpdcache_mem_data_t  ( hpdcache_mem_data_t    ),
      .hpdcache_mem_be_t    ( hpdcache_mem_be_t      ),
      .hpdcache_mem_req_t   ( hpdcache_mem_req_t     ),
      .hpdcache_mem_req_w_t ( hpdcache_mem_req_w_t   ),
      .hpdcache_mem_resp_r_t( hpdcache_mem_resp_r_t  ),
      .hpdcache_mem_resp_w_t( hpdcache_mem_resp_w_t  )
  ) i_hpdcache (
      .clk_i,
      .rst_ni,

      .wbuf_flush_i,

      .core_req_valid_i,
      .core_req_ready_o,
      .core_req_i,
      .core_req_abort_i,
      .core_req_tag_i,
      .core_req_pma_i,

      .core_rsp_valid_o,
      .core_rsp_o,

      .mem_req_read_ready_i,
      .mem_req_read_valid_o,
      .mem_req_read_o,

      .mem_resp_read_ready_o,
      .mem_resp_read_valid_i,
      .mem_resp_read_i,

      .mem_req_write_ready_i,
      .mem_req_write_valid_o,
      .mem_req_write_o,

      .mem_req_write_data_ready_i,
      .mem_req_write_data_valid_o,
      .mem_req_write_data_o,

      .mem_resp_write_ready_o,
      .mem_resp_write_valid_i,
      .mem_resp_write_i,

      .evt_cache_write_miss_o(  /* unused */),
      .evt_cache_read_miss_o (  /* unused */),
      .evt_uncached_req_o    (  /* unused */),
      .evt_cmo_req_o         (  /* unused */),
      .evt_write_req_o       (  /* unused */),
      .evt_read_req_o        (  /* unused */),
      .evt_prefetch_req_o    (  /* unused */),
      .evt_req_on_hold_o     (  /* unused */),
      .evt_rtab_rollback_o   (  /* unused */),
      .evt_stall_refill_o    (  /* unused */),
      .evt_stall_o           (  /* unused */),

      .wbuf_empty_o,

      .cfg_enable_i                       ( 1'b1 ),
      .cfg_wbuf_threshold_i               ( 3'd2 ),
      .cfg_wbuf_reset_timecnt_on_write_i  ( 1'b1 ),
      .cfg_wbuf_sequential_waw_i          ( 1'b0 ),
      .cfg_wbuf_inhibit_write_coalescing_i( 1'b0 ),
      .cfg_prefetch_updt_plru_i           ( 1'b1 ),
      .cfg_error_on_cacheable_amo_i       ( 1'b0 ),
      .cfg_rtab_single_entry_i            ( 1'b0 ),
      .cfg_default_wb_i                   ( 1'b0 )
  );

endmodule : cluster_cache