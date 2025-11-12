// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "common_cells/registers.svh"

/// Instruction Cache
// Simple direct mapped cache
module instruction_cache #(
    /// Width of the Program Counter
    parameter int unsigned PcWidth = 8,
    /// Number of warps per compute unit
    parameter int unsigned NumWarps = 8,
    /// Number of threads per warp
    parameter int unsigned WarpWidth = 32,
    /// Encoded instruction width
    parameter int unsigned EncInstWidth = 4,
    /// Encoded instructions per cacheline -> Also determines the memory interface width
    parameter int unsigned CachelineIdxBits = 2,
    /// Number of cachelines in the instruction cache
    parameter int unsigned NumCachelines = 8,

    /// Dependent parameter, do **not** overwrite.
    parameter int unsigned SubwarpIdWidth     = WarpWidth > 1 ? $clog2(WarpWidth) : 1,
    parameter int unsigned WidWidth           =  NumWarps > 1 ? $clog2(NumWarps)  : 1,
    parameter int unsigned CachelineAddrWidth = PcWidth - CachelineIdxBits,
    parameter type         cache_addr_t = logic [CachelineAddrWidth-1:0],
    parameter type         wid_t        = logic [          WidWidth-1:0],
    parameter type         pc_t         = logic [           PcWidth-1:0],
    parameter type         act_mask_t   = logic [         WarpWidth-1:0],
    parameter type         enc_inst_t   = logic [      EncInstWidth-1:0],
    parameter type         subwarp_id_t = logic [    SubwarpIdWidth-1:0]
) (
    // Clock and reset
    input logic clk_i,
    input logic rst_ni,

    // Flush the cache
    input  logic flush_i,

    // Memory request interface
    input  logic        mem_ready_i,
    output logic        mem_req_o,
    output cache_addr_t mem_addr_o,

    // Memory response interface
    input logic                                    mem_valid_i,
    input enc_inst_t [(1 << CachelineIdxBits)-1:0] mem_data_i,

    // From Fetcher
    output logic        ic_ready_o,
    input  logic        fe_valid_i,
    input  pc_t         fe_pc_i,
    input  act_mask_t   fe_act_mask_i,
    input  wid_t        fe_warp_id_i,
    input  subwarp_id_t fe_subwarp_id_i,

    // To Decode
    input  logic        dec_ready_i,
    output logic        ic_valid_o,
    output pc_t         ic_pc_o,
    output act_mask_t   ic_act_mask_o,
    output wid_t        ic_warp_id_o,
    output enc_inst_t   ic_inst_o,
    output subwarp_id_t ic_subwarp_id_o
);
    // #######################################################################################
    // # Local Parameters                                                                    #
    // #######################################################################################

    // How many bits are needed to select a cacheline?
    localparam int unsigned CacheSelectBits = $clog2(NumCachelines);

    // How wide is the cacheline tag? -> PC = {Tag, CachelineSelectBits, CachelineIdxBits}
    localparam int unsigned CacheTagBits = PcWidth - CachelineIdxBits - CacheSelectBits;

    // #######################################################################################
    // # Typedefs                                                                            #
    // #######################################################################################

    // States
    typedef enum logic [1:0] {
        IDLE             = 'd0, // Idle state, waiting for an instruction to fetch
        HANDLE_INSTR     = 'd1, // We have looked up the tag/data, handle hit/miss
        WAIT_FOR_MEM     = 'd2, // We have sent a memory request, waiting for the response
        WAIT_FOR_DECODER = 'd3  // Waiting for the decoder to be ready to send the next instruction
    } state_e;

    // Fetch request
    typedef struct packed {
        pc_t         pc;         // Program counter of the instruction
        act_mask_t   act_mask;   // Active mask of the warp
        wid_t        warp_id;    // Warp ID of the instruction
        subwarp_id_t subwarp_id; // Subwarp ID of the instruction
    } fetch_req_t;

    // Cache tag
    typedef logic [CacheTagBits-1:0] cache_tag_t;

    // Cacheline select
    typedef logic [CacheSelectBits-1:0] cache_select_t;

    // Cacheline data
    typedef enc_inst_t [(1 << CachelineIdxBits)-1:0] cache_data_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Flush request
    logic flush_q, flush_d;

    // State machine
    state_e state_q, state_d;

    // Active request
    fetch_req_t    active_req_q, active_req_d;
    cache_select_t cache_select; // Which cacheline to select

    logic cache_req, cache_we;
    cache_tag_t write_cache_tag;

    // Output from memories
    logic       cache_valid_q, cache_valid_d;
    cache_tag_t cache_tag_q;
    cache_data_t cache_data;

    cache_data_t mem_data_q, mem_data_d;

    // Valid bits
    logic [NumCachelines-1:0] cache_valids_d, cache_valids_q;

    // #######################################################################################
    // # Combinational Logic                                                                 #
    // #######################################################################################

    always_comb begin : state_logic
        // Default
        state_d        = state_q;
        active_req_d   = active_req_q;
        mem_data_d     = mem_data_q;
        cache_valids_d = cache_valids_q;
        cache_valid_d  = cache_valid_q;
        flush_d        = flush_q;

        // Memory request interface
        mem_req_o  = 1'b0;
        mem_addr_o = '0;

        // Request from Fetcher
        ic_ready_o = 1'b0;

        // Output to decoder
        ic_valid_o      = 1'b0;
        ic_pc_o         = '0;
        ic_act_mask_o   = '0;
        ic_warp_id_o    = '0;
        ic_subwarp_id_o = '0;
        ic_inst_o       = '0;

        // Cache request
        cache_req    = 1'b0; // No lookup
        cache_we     = 1'b0; // No write
        cache_select = '0;   // No cacheline selected

        // New flush request
        if (flush_i) begin
            flush_d = 1'b1;
        end

        // State machine

        // Idle State
        if (state_q == IDLE) begin : idle_state
            // Wait for a valid instruction from the fetcher
            ic_ready_o = 1'b1;

            // Flush the cache if requested
            if (flush_q) begin : idle_flush
                ic_ready_o     = 1'b0; // Not ready for new requests
                cache_valids_d = '0;   // Invalidate all cachelines
                flush_d        = 1'b0; // Reset flush request
            end : idle_flush

            // Handshake -> new request
            else if (fe_valid_i) begin
                // Go to handle instruction state
                state_d = HANDLE_INSTR;

                // Perform cache lookup
                cache_req = 1'b1;
                cache_select = fe_pc_i[CacheSelectBits+CachelineIdxBits-1:
                                      CachelineIdxBits];

                // Lookup valid bit
                cache_valid_d = cache_valids_q[cache_select];

                // Store the active request
                active_req_d.pc         = fe_pc_i;
                active_req_d.act_mask   = fe_act_mask_i;
                active_req_d.warp_id    = fe_warp_id_i;
                active_req_d.subwarp_id = fe_subwarp_id_i;
            end
        end : idle_state

        // Handle instruction state
        else if (state_q == HANDLE_INSTR) begin : handle_instr_state
            // Cache hit
            if (cache_valid_q
                && cache_tag_q == active_req_q.pc[PcWidth-1-:CacheTagBits])
            begin : cache_hit
                // If the cache is valid and the tag matches
                // -> Hit, send to decoder, check if we have a new request

                // Send to decoder
                ic_valid_o      = 1'b1;
                ic_pc_o         = active_req_q.pc;
                ic_act_mask_o   = active_req_q.act_mask;
                ic_warp_id_o    = active_req_q.warp_id;
                ic_subwarp_id_o = active_req_q.subwarp_id;
                ic_inst_o       = cache_data[
                    active_req_q.pc[CachelineIdxBits-1:0]
                ];

                // Handshake with decoder
                if (dec_ready_i) begin
                    ic_ready_o = 1'b1;

                    if (flush_q) begin : flush_cache
                        ic_ready_o     = 1'b0; // Not ready for new requests
                        cache_valids_d = '0;   // Invalidate all cachelines
                        flush_d        = 1'b0; // Reset flush request

                        // Go back to idle state
                        state_d = IDLE;
                    end : flush_cache
                    // Handshake with fetcher -> new request
                    else if (fe_valid_i) begin
                        // Go to handle instruction state
                        state_d = HANDLE_INSTR;

                        // Perform cache lookup
                        cache_req = 1'b1;
                        cache_select = fe_pc_i[CacheSelectBits+CachelineIdxBits-1:
                                              CachelineIdxBits];
                        // Lookup valid bit
                        cache_valid_d = cache_valids_q[cache_select];

                        // Store the active request
                        active_req_d.pc         = fe_pc_i;
                        active_req_d.act_mask   = fe_act_mask_i;
                        active_req_d.warp_id    = fe_warp_id_i;
                        active_req_d.subwarp_id = fe_subwarp_id_i;
                    end else begin
                        // No new request, go back to idle state
                        state_d = IDLE;
                    end
                end
            end : cache_hit

            // Cache miss
            else begin : cache_miss
                // Send memory request, go into wait for memory state upon handshake
                mem_req_o  = 1'b1;
                mem_addr_o = active_req_q.pc[PcWidth-1:CachelineIdxBits];

                // Handshake with memory request interface -> request is sent, wait for response
                if (mem_ready_i) begin
                    state_d = WAIT_FOR_MEM;
                end
            end : cache_miss
        end : handle_instr_state

        // Wait for memory state
        else if (state_q == WAIT_FOR_MEM) begin : wait_for_mem_state
            // Wait for memory response
            if (mem_valid_i) begin
                // Write into cache memory
                cache_req = 1'b1;
                cache_we  = 1'b1;
                cache_select = active_req_q.pc[CacheSelectBits+CachelineIdxBits-1:
                                              CachelineIdxBits];

                // Set valid bit
                cache_valids_d[cache_select] = 1'b1;

                // Store the write data
                mem_data_d = mem_data_i;

                // TODO: We could also return the data immediately to the decoder

                state_d = WAIT_FOR_DECODER;
            end
        end : wait_for_mem_state

        // Wait for decoder state
        else if (state_q == WAIT_FOR_DECODER) begin : wait_for_decoder_state
            ic_valid_o      = 1'b1;
            ic_pc_o         = active_req_q.pc;
            ic_act_mask_o   = active_req_q.act_mask;
            ic_warp_id_o    = active_req_q.warp_id;
            ic_subwarp_id_o = active_req_q.subwarp_id;
            ic_inst_o       = mem_data_q[
                active_req_q.pc[CachelineIdxBits-1:0]
            ];

            // Wait for decoder to be ready
            if (dec_ready_i) begin
                ic_ready_o = 1'b1;

                // Flush
                if (flush_q) begin : wait_for_decoder_flush
                    ic_ready_o     = 1'b0; // Not ready for new requests
                    cache_valids_d = '0; // Invalidate all cachelines
                    flush_d        = 1'b0; // Reset flush request

                    // Go back to idle state
                    state_d = IDLE;
                end : wait_for_decoder_flush
                // Handshake with fetcher -> new request
                else if (fe_valid_i) begin
                    // Go to handle instruction state
                    state_d = HANDLE_INSTR;

                    // Perform cache lookup
                    cache_req = 1'b1;
                    cache_select = fe_pc_i[CacheSelectBits+CachelineIdxBits-1:
                                            CachelineIdxBits];

                    // Lookup valid bit
                    cache_valid_d = cache_valids_q[cache_select];

                    // Store the active request
                    active_req_d.pc         = fe_pc_i;
                    active_req_d.act_mask   = fe_act_mask_i;
                    active_req_d.warp_id    = fe_warp_id_i;
                    active_req_d.subwarp_id = fe_subwarp_id_i;
                end else begin
                    // No new request, go back to idle state
                    state_d = IDLE;
                end
            end
        end : wait_for_decoder_state

    end : state_logic

    // // Direct mapped -> select the cacheline based on the PC of the active request
    // assign cache_select = active_req_q.pc[CacheSelectBits+CachelineIdxBits-1:
    //                                      CachelineIdxBits];

    // Cache write tag
    assign write_cache_tag =   // Get the tag from pc of the active request
        active_req_q.pc[PcWidth-1:CachelineIdxBits+CacheSelectBits];

    // #######################################################################################
    // # Memories                                                                            #
    // #######################################################################################

    // Tag memory
    tc_sram #(
        .NumWords   ( NumCachelines      ),
        .DataWidth  ( $bits(cache_tag_t) ),
        .ByteWidth  ( $bits(cache_tag_t) ),
        .NumPorts   ( 1                  ),
        .Latency    ( 1                  ),
        .SimInit    ( "zeros"            ),
        .PrintSimCfg( 1'b1               ),
        .ImplKey    ( "i_cache_tag_mem"  )
    ) i_tag_mem (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .req_i  ( cache_req    ),
        .we_i   ( cache_we     ),
        .addr_i ( cache_select ),
        .wdata_i( write_cache_tag ),

        .rdata_o( cache_tag_q ),

        // Always write entire word
        .be_i ( '1 )
    );

    // Valid FFs
    `FF(cache_valid_q,  cache_valid_d,  '0, clk_i, rst_ni)
    `FF(cache_valids_q, cache_valids_d, '0, clk_i, rst_ni)

    // Instruction memory
    tc_sram #(
        .NumWords   ( NumCachelines                          ),
        .DataWidth  ( (1 << CachelineIdxBits) * EncInstWidth ),
        .ByteWidth  ( 8                                      ),
        .NumPorts   ( 1                                      ),
        .Latency    ( 1                                      ),
        .SimInit    ( "zeros"                                ),
        .PrintSimCfg( 1'b1                                   ),
        .ImplKey    ( "i_cache_inst_mem"                     )
    ) i_inst_mem (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .req_i  ( cache_req    ),
        .we_i   ( cache_we     ),
        .addr_i ( cache_select ),
        .wdata_i( mem_data_i   ),

        .rdata_o( cache_data ),

        // Always write entire word
        .be_i ( '1 )
    );

    // #######################################################################################
    // # Sequential Logic                                                                    #
    // #######################################################################################

    // Flush request
    `FF(flush_q, flush_d, 1'b0, clk_i, rst_ni)

    // State machine
    `FF(state_q, state_d, IDLE, clk_i, rst_ni)

    // Active request
    `FF(active_req_q, active_req_d, '0, clk_i, rst_ni)

    // Data from memory
    `FF(mem_data_q, mem_data_d, '0, clk_i, rst_ni)

    // #######################################################################################
    // # Assertions                                                                          #
    // #######################################################################################

    // TODO: These are not exhaustive
    `ifndef SYNTHESIS
        /// Check if new state is valid given the current state
        // From IDLE state
        assert property (@(posedge clk_i) disable iff (!rst_ni)
            !(state_q == IDLE) || (state_d == IDLE || state_d == HANDLE_INSTR)
        ) else $fatal(1, "Invalid state transition from IDLE state to %0d", state_d);
        // From HANDLE_INSTR state
        assert property (@(posedge clk_i) disable iff (!rst_ni)
            !(state_q == HANDLE_INSTR) || (state_d == IDLE || state_d == HANDLE_INSTR
                                           || state_d == WAIT_FOR_MEM)
        ) else $fatal(1, "Invalid state transition from HANDLE_INSTR state to %0d", state_d);
        // From WAIT_FOR_MEM state
        assert property (@(posedge clk_i) disable iff (!rst_ni)
            !(state_q == WAIT_FOR_MEM) || (state_d == WAIT_FOR_MEM || state_d == WAIT_FOR_DECODER)
        ) else $fatal(1, "Invalid state transition from WAIT_FOR_MEM state to %0d", state_d);
        // From WAIT_FOR_DECODER state
        assert property (@(posedge clk_i) disable iff (!rst_ni)
            !(state_q == WAIT_FOR_DECODER) || (state_d == IDLE || state_d == HANDLE_INSTR
                                               || state_d == WAIT_FOR_DECODER)
        ) else $fatal(1, "Invalid state transition from WAIT_FOR_DECODER state to %0d", state_d);

        /// Memory interface assertions
        // Ensure that we only receive memory responses in the WAIT_FOR_MEM state
        assert property (@(posedge clk_i) disable iff (!rst_ni)
            !mem_valid_i || (state_q == WAIT_FOR_MEM)
        ) else $fatal(1, "Memory response received, but not in WAIT_FOR_MEM state.");

        // Ensure that we only send memory requests in the HANDLE_INSTR state
        assert property (@(posedge clk_i) disable iff (!rst_ni)
            !mem_req_o || (state_q == HANDLE_INSTR)
        ) else $fatal(1, "Memory request sent, but not in HANDLE_INSTR state.");

        // If we sent out a memory request, we must got to the WAIT_FOR_MEM state
        assert property (@(posedge clk_i) disable iff (!rst_ni)
            !(mem_req_o && mem_ready_i) || (state_d == WAIT_FOR_MEM)
        ) else $fatal(1, "Memory request sent, but did not go to WAIT_FOR_MEM state.");

        // If decoder is not ready, the output must stay stable and valid
        assert property (@(posedge clk_i)
            !$past(ic_valid_o && !dec_ready_i && rst_ni) || !rst_ni
                || (ic_valid_o && $stable({ic_pc_o, ic_act_mask_o, ic_warp_id_o,
                                          ic_subwarp_id_o, ic_inst_o}))
        ) else $fatal(1, "Decoder not ready, but output changed.");
    `endif

    // #######################################################################################
    // # Formal Properties                                                                   #
    // #######################################################################################

    `ifdef FORMAL
        /// Check that we can reach all states
        cover property (@(posedge clk_i) disable iff (!rst_ni) (state_q == IDLE));
        cover property (@(posedge clk_i) disable iff (!rst_ni) (state_q == HANDLE_INSTR));
        cover property (@(posedge clk_i) disable iff (!rst_ni) (state_q == WAIT_FOR_MEM));
        cover property (@(posedge clk_i) disable iff (!rst_ni) (state_q == WAIT_FOR_DECODER));

        /// Check that we can perform all transitions
        // IDLE state
        cover property (@(posedge clk_i) disable iff (!rst_ni) (state_q == IDLE)
            && (state_d == HANDLE_INSTR));
        // HANDLE_INSTR state
        cover property (@(posedge clk_i) disable iff (!rst_ni) (state_q == HANDLE_INSTR)
            && (state_d == IDLE));
        cover property (@(posedge clk_i) disable iff (!rst_ni) (state_q == HANDLE_INSTR)
            && (state_d == HANDLE_INSTR));
        cover property (@(posedge clk_i) disable iff (!rst_ni) (state_q == HANDLE_INSTR)
            && (state_d == WAIT_FOR_MEM));
        // WAIT_FOR_MEM state
        cover property (@(posedge clk_i) disable iff (!rst_ni) (state_q == WAIT_FOR_MEM)
            && (state_d == WAIT_FOR_MEM));
        cover property (@(posedge clk_i) disable iff (!rst_ni) (state_q == WAIT_FOR_MEM)
            && (state_d == WAIT_FOR_DECODER));
        // WAIT_FOR_DECODER state
        cover property (@(posedge clk_i) disable iff (!rst_ni) (state_q == WAIT_FOR_DECODER)
            && (state_d == IDLE));
        cover property (@(posedge clk_i) disable iff (!rst_ni) (state_q == WAIT_FOR_DECODER)
            && (state_d == HANDLE_INSTR));
        cover property (@(posedge clk_i) disable iff (!rst_ni) (state_q == WAIT_FOR_DECODER)
            && (state_d == WAIT_FOR_DECODER));

        /// Cover Handshakes
        // Check that we can perform memory requests
        cover property (@(posedge clk_i) disable iff (!rst_ni) (mem_req_o && mem_ready_i));
        cover property (@(posedge clk_i) disable iff (!rst_ni) (!mem_req_o && mem_ready_i));
        // Check that we can receive memory responses
        cover property (@(posedge clk_i) disable iff (!rst_ni) (mem_valid_i));
        cover property (@(posedge clk_i) disable iff (!rst_ni) (!mem_valid_i));
        // Check that we can receive a new instruction
        cover property (@(posedge clk_i) disable iff (!rst_ni) (fe_valid_i && ic_ready_o));
        cover property (@(posedge clk_i) disable iff (!rst_ni) (fe_valid_i && !ic_ready_o));
        // Check that we can send an instruction to the decoder
        cover property (@(posedge clk_i) disable iff (!rst_ni) (ic_valid_o && dec_ready_i));
        cover property (@(posedge clk_i) disable iff (!rst_ni) (!ic_valid_o && dec_ready_i));

        /// Memory Latency Model
        localparam int unsigned FormalMemLatency = 3;
        logic [FormalMemLatency-1:0] fv_mem_req_shift;
        cache_addr_t [FormalMemLatency-1:0] fv_mem_addr_shift;
        always_ff @(posedge clk_i or negedge rst_ni) begin
            if (!rst_ni) begin
                fv_mem_req_shift  <= '0;
                fv_mem_addr_shift <= '0;
            end else begin
                fv_mem_req_shift <= {fv_mem_req_shift[FormalMemLatency-2:0],
                                    mem_req_o && mem_ready_i};
                fv_mem_addr_shift <= {fv_mem_addr_shift[FormalMemLatency-2:0],
                                     mem_addr_o};
            end
        end

        // Memory valid signal must be delayed version of mem_req_o && mem_ready_i
        assume property (@(posedge clk_i) disable iff (!rst_ni)
            (mem_valid_i == fv_mem_req_shift[FormalMemLatency-1]));

        // There can only be one active memory request at a time
        assert property (@(posedge clk_i) $onehot0(fv_mem_req_shift));

        // New request
        cache_addr_t f_mem_addr;
        cache_data_t f_mem_data;
        act_mask_t   f_act_mask;
        wid_t        f_warp_id;
        subwarp_id_t f_subwarp_id;

        assign f_mem_addr   = $anyconst;
        assign f_mem_data   = $anyconst;
        assign f_act_mask   = $anyconst;
        assign f_warp_id    = $anyconst;
        assign f_subwarp_id = $anyconst;

        // Assume that if the fetcher request the instruction with f_pc, we have a request with f_* signals
        logic fetcher_request_matches_f_pc;
        assign fetcher_request_matches_f_pc =
            fe_valid_i && (fe_pc_i[PcWidth-1:CachelineIdxBits] == f_mem_addr);
        assume property (@(posedge clk_i) disable iff (!rst_ni)
            !fetcher_request_matches_f_pc || (fe_act_mask_i == f_act_mask)
        );
        assume property (@(posedge clk_i) disable iff (!rst_ni)
            !fetcher_request_matches_f_pc || (fe_warp_id_i == f_warp_id)
        );
        assume property (@(posedge clk_i) disable iff (!rst_ni)
            !fetcher_request_matches_f_pc || (fe_subwarp_id_i == f_subwarp_id)
        );

        // Assert that valid cachelines that match the assumed memory address return the correct data
        cache_addr_t [NumCachelines-1:0] cacheline_addrs;
        logic [NumCachelines-1:0]        cacheline_matches;
        for (genvar i = 0; i < NumCachelines; i++) begin : gen_cacheline_addrs
            assign cacheline_addrs[i] = {
                i_tag_mem.sram[i],
                cache_select_t'(i)
            };
            assign cacheline_matches[i] = (cacheline_addrs[i] == f_mem_addr) && cache_valids_q[i];

            assert property (@(posedge clk_i) disable iff (!rst_ni)
                !(cacheline_matches[i]) || (f_mem_data == i_inst_mem.sram[i])
            ) else $fatal(1, "Memory data does not match cache data for matching addresses.");
        end

        logic request_matches_addr;
        assign request_matches_addr = mem_valid_i
            && (fv_mem_addr_shift[FormalMemLatency-1] == f_mem_addr);
        assume property (@(posedge clk_i) disable iff (!rst_ni)
            !request_matches_addr || (mem_data_i == f_mem_data)
        ) else $fatal(1, "Memory data does not match assumed data.");

        // If instruction has the same address as our assumed memory address, the data must match
        logic result_matches_mem_addr;
        assign result_matches_mem_addr = ic_valid_o
            && (ic_pc_o[PcWidth-1:CachelineIdxBits] == f_mem_addr);
        enc_inst_t result_exp_inst;
        assign result_exp_inst = f_mem_data[
            ic_pc_o[CachelineIdxBits-1:0]
        ];
        assert property (@(posedge clk_i) disable iff (!rst_ni)
            !result_matches_mem_addr || (ic_inst_o == result_exp_inst)
        ) else $fatal(1, "Instruction data does not match memory data for matching addresses.");

        // Other signals must also match the f_* signals
        assert property (@(posedge clk_i) disable iff (!rst_ni)
            !result_matches_mem_addr || (ic_act_mask_o == f_act_mask)
        ) else $fatal(1, "Active mask does not match assumed data.");
        assert property (@(posedge clk_i) disable iff (!rst_ni)
            !result_matches_mem_addr || (ic_warp_id_o == f_warp_id)
        ) else $fatal(1, "Warp ID does not match assumed data.");
        assert property (@(posedge clk_i) disable iff (!rst_ni)
            !result_matches_mem_addr || (ic_subwarp_id_o == f_subwarp_id)
        ) else $fatal(1, "Subwarp ID does not match assumed data.");

        logic active_req_matches_mem_addr;
        assign active_req_matches_mem_addr =
            (active_req_q.pc[PcWidth-1:CachelineIdxBits] == f_mem_addr);

        // Cache miss -> data came from memory
        assert property (@(posedge clk_i) disable iff (!rst_ni)
            !(active_req_matches_mem_addr && state_q == WAIT_FOR_DECODER)
            || (mem_data_q == f_mem_data)
        ) else $fatal(1, "Stored memory data does not match assumed data.");

        // Data in active request must match f_* signals
        assert property (@(posedge clk_i) disable iff (!rst_ni)
            !(active_req_matches_mem_addr && (state_q != IDLE))
            || (active_req_q.act_mask == f_act_mask)
        ) else $fatal(1, "Active mask does not match assumed data on cache miss.");

        assert property (@(posedge clk_i) disable iff (!rst_ni)
            !(active_req_matches_mem_addr && (state_q != IDLE))
            || (active_req_q.warp_id == f_warp_id)
        ) else $fatal(1, "Warp ID does not match assumed data on cache miss.");

        assert property (@(posedge clk_i) disable iff (!rst_ni)
            !(active_req_matches_mem_addr && (state_q != IDLE))
            || (active_req_q.subwarp_id == f_subwarp_id)
        ) else $fatal(1, "Subwarp ID does not match assumed data on cache miss.");

        // Cache hit -> data came from cache
        logic cache_hit_matches_mem_addr;
        assign cache_hit_matches_mem_addr = cache_valid_q
            && (cache_tag_q == active_req_q.pc[PcWidth-1-:CacheTagBits])
            && active_req_matches_mem_addr;

        assert property (@(posedge clk_i) disable iff (!rst_ni)
            !(state_q == HANDLE_INSTR && ic_valid_o && cache_hit_matches_mem_addr)
            || (cache_data == f_mem_data)
        ) else $fatal(1, "Cache data does not match assumed data.");
    `endif

endmodule : instruction_cache
