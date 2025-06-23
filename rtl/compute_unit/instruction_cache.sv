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
    parameter int unsigned WidWidth           =         NumWarps > 1 ? $clog2(NumWarps) : 1,
    parameter int unsigned CachelineAddrWidth = CachelineIdxBits > 0 ? PcWidth - CachelineIdxBits
                                                    : PcWidth,
    parameter type         cache_addr_t = logic [CachelineAddrWidth-1:0],
    parameter type         wid_t        = logic [          WidWidth-1:0],
    parameter type         pc_t         = logic [           PcWidth-1:0],
    parameter type         act_mask_t   = logic [         WarpWidth-1:0],
    parameter type         enc_inst_t   = logic [      EncInstWidth-1:0]
) (
    // Clock and reset
    input logic clk_i,
    input logic rst_ni,

    // Memory request interface
    input  logic        mem_ready_i,
    output logic        mem_req_o,
    output cache_addr_t mem_addr_o,

    // Memory response interface
    input logic                                    mem_valid_i,
    input enc_inst_t [(1 << CachelineIdxBits)-1:0] mem_data_i,

    // From Fetcher
    output logic      ic_ready_o,
    input  logic      fe_valid_i,
    input  pc_t       fe_pc_i,
    input  act_mask_t fe_act_mask_i,
    input  wid_t      fe_warp_id_i,

    // To Decode
    input  logic      dec_ready_i,
    output logic      ic_valid_o,
    output pc_t       ic_pc_o,
    output act_mask_t ic_act_mask_o,
    output wid_t      ic_warp_id_o,
    output enc_inst_t ic_inst_o
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
        pc_t       pc;         // Program counter of the instruction
        act_mask_t act_mask;   // Active mask of the warp
        wid_t      warp_id;    // Warp ID of the instruction
    } fetch_req_t;

    // Cache tag
    typedef logic [CacheTagBits-1:0] cache_tag_t;

    // Cacheline select
    typedef logic [CacheSelectBits-1:0] cache_select_t;

    // Valid Tag data
    typedef struct packed {
        logic       valid;
        cache_tag_t cache_tag;
    } valid_tag_t;

    // Cacheline data
    typedef enc_inst_t [(1 << CachelineIdxBits)-1:0] cache_data_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // State machine
    state_e state_q, state_d;

    // Active request
    fetch_req_t    active_req_q, active_req_d;
    cache_select_t cache_select; // Which cacheline to select

    logic cache_req, cache_we;
    valid_tag_t write_cache_valid_tag;

    // Output from memories
    valid_tag_t cache_valid_tag;
    cache_data_t cache_data;

    cache_data_t mem_data_q, mem_data_d;

    // #######################################################################################
    // # Combinational Logic                                                                 #
    // #######################################################################################

    always_comb begin : state_logic
        // Default
        state_d      = state_q;
        active_req_d = active_req_q;
        mem_data_d   = mem_data_q;

        // Memory request interface
        mem_req_o  = 1'b0;
        mem_addr_o = '0;

        // Request from Fetcher
        ic_ready_o = 1'b0;

        // Output to decoder
        ic_valid_o    = 1'b0;
        ic_pc_o       = '0;
        ic_act_mask_o = '0;
        ic_warp_id_o  = '0;
        ic_inst_o     = '0;

        // Cache request
        cache_req    = 1'b0; // No lookup
        cache_we     = 1'b0; // No write
        cache_select = '0;   // No cacheline selected

        // State machine

        // Idle State
        if (state_q == IDLE) begin : idle_state
            // Wait for a valid instruction from the fetcher
            ic_ready_o = 1'b1;

            // Handshake -> new request
            if (fe_valid_i) begin
                // Go to handle instruction state
                state_d = HANDLE_INSTR;

                // Perform cache lookup
                cache_req = 1'b1;
                cache_select = fe_pc_i[CacheSelectBits+CachelineIdxBits-1:
                                      CachelineIdxBits];

                // Store the active request
                active_req_d.pc       = fe_pc_i;
                active_req_d.act_mask = fe_act_mask_i;
                active_req_d.warp_id  = fe_warp_id_i;
            end
        end : idle_state

        // Handle instruction state
        else if (state_q == HANDLE_INSTR) begin : handle_instr_state
            // Cache hit
            if (cache_valid_tag.valid
                && cache_valid_tag.cache_tag == active_req_q.pc[PcWidth-1-:CacheTagBits])
            begin : cache_hit
                // If the cache is valid and the tag matches
                // -> Hit, send to decoder, check if we have a new request

                // Send to decoder
                ic_valid_o    = 1'b1;
                ic_pc_o       = active_req_q.pc;
                ic_act_mask_o = active_req_q.act_mask;
                ic_warp_id_o  = active_req_q.warp_id;
                ic_inst_o     = cache_data[
                    active_req_q.pc[CachelineIdxBits-1:0]
                ];

                // Handle next instruction request if decoder is ready
                // Handshake with decoder
                if (dec_ready_i) begin
                    ic_ready_o = 1'b1;
                    // Handshake with fetcher -> new request
                    if (fe_valid_i) begin
                        // Go to handle instruction state
                        state_d = HANDLE_INSTR;

                        // Perform cache lookup
                        cache_req = 1'b1;
                        cache_select = fe_pc_i[CacheSelectBits+CachelineIdxBits-1:
                                              CachelineIdxBits];

                        // Store the active request
                        active_req_d.pc       = fe_pc_i;
                        active_req_d.act_mask = fe_act_mask_i;
                        active_req_d.warp_id  = fe_warp_id_i;
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

                // Store the write data
                mem_data_d = mem_data_i;

                // TODO: We could also return the data immediately to the decoder

                state_d = WAIT_FOR_DECODER;
            end
        end : wait_for_mem_state

        // Wait for decoder state
        else if (state_q == WAIT_FOR_DECODER) begin : wait_for_decoder_state
            ic_valid_o = 1'b1;
            ic_pc_o    = active_req_q.pc;
            ic_act_mask_o = active_req_q.act_mask;
            ic_warp_id_o  = active_req_q.warp_id;
            ic_inst_o     = mem_data_q[
                active_req_q.pc[CachelineIdxBits-1:0]
            ];

            // Wait for decoder to be ready
            if (dec_ready_i) begin
                ic_ready_o = 1'b1;
                // Handshake with fetcher -> new request
                if (fe_valid_i) begin
                    // Go to handle instruction state
                    state_d = HANDLE_INSTR;

                    // Perform cache lookup
                    cache_req = 1'b1;
                    cache_select = fe_pc_i[CacheSelectBits+CachelineIdxBits-1:
                                            CachelineIdxBits];

                    // Store the active request
                    active_req_d.pc       = fe_pc_i;
                    active_req_d.act_mask = fe_act_mask_i;
                    active_req_d.warp_id  = fe_warp_id_i;
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

    // Cache write valid and tag
    assign write_cache_valid_tag.valid = 1'b1; // Valid bit is set
    assign write_cache_valid_tag.cache_tag =   // Get the tag from pc of the active request
        active_req_q.pc[PcWidth-1:CachelineIdxBits+CacheSelectBits];

    // #######################################################################################
    // # Memories                                                                            #
    // #######################################################################################

    // Tag and Valid memory
    tc_sram #(
        .NumWords   ( NumCachelines      ),
        .DataWidth  ( $bits(valid_tag_t) ),
        .ByteWidth  ( 1                  ),
        .NumPorts   ( 1                  ),
        .Latency    ( 1                  ),
        .SimInit    ( "zeros"            ),
        .PrintSimCfg( 1'b1               ),
        .ImplKey    ( "i_cache_tag_mem"  )
    ) i_tag_mem (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .req_i  ( cache_req             ),
        .we_i   ( cache_we              ),
        .addr_i ( cache_select          ),
        // .wdata_i (),
        .wdata_i( write_cache_valid_tag ),

        .rdata_o( cache_valid_tag ),

        // Always write entire word
        .be_i ( '1 )
    );

    // Valid bits have to be set to zero upon reset
    // This might require special logic for ASIC implementations -> FFs array for valid bits
    `ifdef TARGET_ASIC
        initial $fatal("Instruction cache tag memory not implemented for ASIC targets.");
    `endif

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

    // State machine
    `FF(state_q, state_d, IDLE, clk_i, rst_ni);

    // Active request
    `FF(active_req_q, active_req_d, '0, clk_i, rst_ni);

    `FF(mem_data_q, mem_data_d, '0, clk_i, rst_ni);

endmodule : instruction_cache
