// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "common_cells/registers.svh"

/// Instruction Cache
// Simple direct mapped cache
module instruction_cache #(
    /// Width of the Program Counter
    parameter int unsigned PcWidth = 32,
    /// Number of warps per compute unit
    parameter int unsigned NumWarps = 8,
    /// Number of threads per warp
    parameter int unsigned WarpWidth = 32,
    /// Encoded instruction width
    parameter int unsigned EncInstWidth = 32,
    /// Encoded instructions per cacheline -> Also determines the memory interface width
    parameter int unsigned CachelineIdxBits = 1,
    /// Number of cachelines in the instruction cache
    parameter int unsigned NumCachelines = 32,

    /// Dependent parameter, do **not** overwrite.
    parameter int unsigned SubwarpIdWidth     =        WarpWidth > 1 ? $clog2(WarpWidth) : 1,
    parameter int unsigned WidWidth           =         NumWarps > 1 ? $clog2(NumWarps)  : 1,
    parameter int unsigned CachelineAddrWidth = CachelineIdxBits > 0 ? PcWidth - CachelineIdxBits
                                                    : PcWidth,
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
        .ByteWidth  ( 1                  ),
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
    `FF(cache_valid_q,  cache_valid_d,  '0, clk_i, rst_ni);
    `FF(cache_valids_q, cache_valids_d, '0, clk_i, rst_ni);

    // Instruction memory
    tc_sram #(
        .NumWords   ( NumCachelines                          ),
        .DataWidth  ( (1 << CachelineIdxBits) * EncInstWidth ),
        .ByteWidth  ( 1                                      ),
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
    `FF(flush_q, flush_d, 1'b0, clk_i, rst_ni);

    // State machine
    `FF(state_q, state_d, IDLE, clk_i, rst_ni);

    // Active request
    `FF(active_req_q, active_req_d, '0, clk_i, rst_ni);

    // Data from memory
    `FF(mem_data_q, mem_data_d, '0, clk_i, rst_ni);

    // #######################################################################################
    // # Assertions                                                                          #
    // #######################################################################################

    `ifndef SYNTHESIS
        assert property (@(posedge clk_i) disable iff (!rst_ni)
            mem_valid_i |-> state_q == WAIT_FOR_MEM
        ) else $fatal("Memory response received, but not in WAIT_FOR_MEM state.");
    `endif

endmodule : instruction_cache
