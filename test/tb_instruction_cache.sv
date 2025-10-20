// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Testbench for Instruction Cache
module tb_instruction_cache import bgpu_pkg::*; #(
    /// Number of instructions to fetch for the warp
    parameter int unsigned FetchWidth = 4,
    /// Width of the Program Counter
    parameter int unsigned PcWidth = 9,
    /// Number of warps
    parameter int unsigned NumWarps = 16,
    /// Number of threads per warp
    parameter int unsigned WarpWidth = 4,
    /// Encoded instructions per cacheline -> Also determines the memory interface width
    parameter int unsigned CachelineIdxBits = 2,
    /// Number of cachelines in the instruction cache
    parameter int unsigned NumCachelines = 16,
    /// Width of an encoded instruction
    parameter int unsigned EncInstWidth = 32,

    /// Number of instructions to process
    parameter int unsigned NumInsts = 10000,

    parameter time         TclkPeriod       = 10ns,
    parameter time         AcqDelay         = 9ns,
    parameter time         ApplDelay        = 1ns,
    parameter int unsigned MaxMstWaitCycles = 1,
    parameter int unsigned MaxSimCycles     = 100000,
    parameter int unsigned WatchdogTimeout  = 1000
);
    // #######################################################################################
    // # Local Parameters                                                                    #
    // #######################################################################################

    localparam int unsigned SubwarpIdWidth = WarpWidth > 1 ? $clog2(WarpWidth) : 1;
    localparam int unsigned WidWidth       =  NumWarps > 1 ? $clog2(NumWarps)  : 1;

    localparam int unsigned CachelineAddrWidth = CachelineIdxBits > 0 ? PcWidth - CachelineIdxBits
                                                    : PcWidth;

    // #######################################################################################
    // # Type Definitions                                                                    #
    // #######################################################################################

    typedef logic [          WidWidth-1:0] wid_t;
    typedef logic [           PcWidth-1:0] pc_t;
    typedef logic [         WarpWidth-1:0] act_mask_t;
    typedef logic [      EncInstWidth-1:0] enc_inst_t;
    typedef logic [    SubwarpIdWidth-1:0] subwarp_id_t;
    typedef logic [CachelineAddrWidth-1:0] cache_addr_t;
    typedef logic [        FetchWidth-1:0] fetch_mask_t;

    // Request from fetcher
    typedef struct packed {
        pc_t         pc;
        act_mask_t   act_mask;
        wid_t        wid;
        subwarp_id_t subwarp_id;
    } fetch_req_t;

    // Response to Decoder
    typedef struct packed {
        logic [FetchWidth-1:0] valid;
        fetch_mask_t fetch_mask;
        pc_t         pc;
        act_mask_t   act_mask;
        wid_t        wid;
        subwarp_id_t subwarp_id;
        enc_inst_t [FetchWidth-1:0] enc_inst;
    } ic_rsp_t;

    // Memory response
    typedef enc_inst_t [(1 << CachelineIdxBits)-1:0] mem_rsp_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Clock and Reset
    logic clk, rst_n;

    // Flush
    logic flush;

    // New request from fetcher
    logic        fetch_req_valid, ic_ready;
    fetch_req_t  fetch_req;
    fetch_mask_t fetch_req_fetch_mask;

    // Response to decoder
    logic [FetchWidth-1:0] ic_valid;
    logic dec_ready;
    ic_rsp_t ic_rsp;

    // Memory interface
    logic        mem_req_valid, mem_ready;
    cache_addr_t mem_req_addr;

    logic     mem_rsp_valid;
    mem_rsp_t mem_rsp;

    // Memory data
    enc_inst_t [(1 << PcWidth)-1:0] mem_data;

    // Golden response
    ic_rsp_t golden_rsp[$];

    // #######################################################################################
    // # Clock generation                                                                    #
    // #######################################################################################

    clk_rst_gen #(
        .ClkPeriod   ( TclkPeriod ),
        .RstClkCycles( 3          )
    ) i_clk_rst_gen (
        .clk_o ( clk   ),
        .rst_no( rst_n )
    );

    // #######################################################################################
    // # Stream Masters and Subordinates                                                     #
    // #######################################################################################

    // Flush logic
    initial begin : flush_logic
        while (1) begin
            @(posedge clk);
            #ApplDelay;
            flush = $urandom_range(0, 64) == 0; // Randomly flush the cache
        end
    end : flush_logic

    // Fetch request
    rand_stream_mst #(
        .data_t       ( fetch_req_t      ),
        .ApplDelay    ( ApplDelay        ),
        .AcqDelay     ( AcqDelay         ),
        .MinWaitCycles( 0                ),
        .MaxWaitCycles( MaxMstWaitCycles )
    ) i_fetch_req (
        .clk_i  ( clk             ),
        .rst_ni ( rst_n           ),
        .valid_o( fetch_req_valid ),
        .data_o ( fetch_req       ),
        .ready_i( ic_ready        )
    );

    initial begin : gen_fetch_mask
        int rand_val;
        fetch_req_fetch_mask = '0;

        while (1) begin
            @(posedge clk);
            #ApplDelay;
            rand_val = $urandom_range(1, (1 << FetchWidth) - 1);
            fetch_req_fetch_mask = '0;
            for (int fidx = 0; fidx < FetchWidth; fidx++)
                if (fidx < FetchWidth)
                    fetch_req_fetch_mask[fidx] = 1'b1;
        end
    end : gen_fetch_mask

    // Response to decoder
    rand_stream_slv #(
        .data_t       ( ic_rsp_t         ),
        .ApplDelay    ( ApplDelay        ),
        .AcqDelay     ( AcqDelay         ),
        .MinWaitCycles( 1                ),
        .MaxWaitCycles( MaxMstWaitCycles ),
        .Enqueue      ( 1'b1             )
    ) i_ic_rsp_to_decoder (
        .clk_i  ( clk       ),
        .rst_ni ( rst_n     ),
        .data_i ( ic_rsp    ),
        .valid_i( |ic_valid ),
        .ready_o( dec_ready )
    );

    // Memory request
    rand_stream_slv #(
        .data_t       ( cache_addr_t     ),
        .ApplDelay    ( ApplDelay        ),
        .AcqDelay     ( AcqDelay         ),
        .MinWaitCycles( 1                ),
        .MaxWaitCycles( MaxMstWaitCycles ),
        .Enqueue      ( 1'b1             )
    ) i_mem_req_sub (
        .clk_i  ( clk           ),
        .rst_ni ( rst_n         ),
        .data_i ( mem_req_addr  ),
        .valid_i( mem_req_valid ),
        .ready_o( mem_ready     )
    );


    initial begin : memory_response
        cache_addr_t addr;

        // Initialize memory with random instructions
        for (int i = 0; i < (1 << PcWidth); i++) begin
            mem_data[i] = $urandom;
        end

        while (1) begin
            @(posedge clk);
            #ApplDelay;
            mem_rsp_valid = 1'b0;
            if (i_mem_req_sub.gen_queue.queue.size() > 0) begin
                mem_rsp_valid = 1'b1;
                addr = i_mem_req_sub.gen_queue.queue.pop_front();

                // Generate memory response based on the address
                for (int j = 0; j < (1 << CachelineIdxBits); j++) begin
                    mem_rsp[j] = mem_data[addr * (1 << CachelineIdxBits) + j];
                end
            end
        end
    end : memory_response

    initial begin : golden_model
        ic_rsp_t grsp;

        while (1) begin
            @(posedge clk);
            #AcqDelay;
            if (fetch_req_valid && ic_ready) begin
                grsp.fetch_mask = fetch_req_fetch_mask;
                grsp.pc         = fetch_req.pc;
                grsp.act_mask   = fetch_req.act_mask;
                grsp.wid        = fetch_req.wid;
                grsp.subwarp_id = fetch_req.subwarp_id;

                grsp.valid    = '0;
                grsp.enc_inst = '0;

                // First pc is always in cacheline
                grsp.valid   [0] = fetch_req_fetch_mask[0];
                grsp.enc_inst[0] = mem_data[fetch_req.pc];

                // Others are valid as long as pc + fidx is within a cacheline
                for (int fidx = 1; fidx < FetchWidth; fidx++) begin
                    if ((int'(fetch_req.pc[CachelineIdxBits-1:0]) + fidx)
                            < (1 << CachelineIdxBits)) begin
                        grsp.valid   [fidx] = fetch_req_fetch_mask[fidx];
                        grsp.enc_inst[fidx] = mem_data[fetch_req.pc + pc_t'(fidx)];
                    end
                end

                $display("Gold Model - Valid: %b, PC: %0h, Warp ID: %0d, Active Mask: %0b, Inst: ",
                         grsp.valid, grsp.pc, grsp.wid, grsp.act_mask);
                for (int fidx = 0; fidx < FetchWidth; fidx++)
                    $display("[%d]: %0h", fidx, grsp.enc_inst[fidx]);

                // Push to golden response queue
                golden_rsp.push_back(grsp);
            end
        end
    end : golden_model

    // #######################################################################################
    // # Watchdog                                                                            #
    // #######################################################################################

    stream_watchdog #(
        .NumCycles( WatchdogTimeout )
    ) i_fetch_watchdog (
        .clk_i  ( clk             ),
        .rst_ni ( rst_n           ),
        .valid_i( fetch_req_valid ),
        .ready_i( ic_ready        )
    );

    stream_watchdog #(
        .NumCycles( WatchdogTimeout )
    ) i_decoder_watchdog (
        .clk_i  ( clk       ),
        .rst_ni ( rst_n     ),
        .valid_i( |ic_valid ),
        .ready_i( dec_ready )
    );

    stream_watchdog #(
        .NumCycles( WatchdogTimeout )
    ) i_mem_req_watchdog (
        .clk_i  ( clk           ),
        .rst_ni ( rst_n         ),
        .valid_i( mem_req_valid ),
        .ready_i( mem_ready     )
    );

    stream_watchdog #(
        .NumCycles( WatchdogTimeout )
    ) i_mem_rsp_watchdog (
        .clk_i  ( clk           ),
        .rst_ni ( rst_n         ),
        .valid_i( mem_rsp_valid ),
        .ready_i( 1'b1          )
    );

    // #######################################################################################
    // # DUT                                                                                 #
    // #######################################################################################

    instruction_cache #(
        .FetchWidth      ( FetchWidth       ),
        .PcWidth         ( PcWidth          ),
        .NumWarps        ( NumWarps         ),
        .WarpWidth       ( WarpWidth        ),
        .EncInstWidth    ( EncInstWidth     ),
        .CachelineIdxBits( CachelineIdxBits ),
        .NumCachelines   ( NumCachelines    )
    ) i_instruction_cache (
        .clk_i ( clk   ),
        .rst_ni( rst_n ),

        .flush_i( flush ),

        .mem_ready_i( mem_ready     ),
        .mem_req_o  ( mem_req_valid ),
        .mem_addr_o ( mem_req_addr  ),

        .mem_valid_i( mem_rsp_valid ),
        .mem_data_i ( mem_rsp       ),

        .ic_ready_o     ( ic_ready             ),
        .fe_valid_i     ( fetch_req_valid      ),
        .fe_fetch_mask_i( fetch_req_fetch_mask ),
        .fe_pc_i        ( fetch_req.pc         ),
        .fe_act_mask_i  ( fetch_req.act_mask   ),
        .fe_warp_id_i   ( fetch_req.wid        ),
        .fe_subwarp_id_i( fetch_req.subwarp_id ),

        .dec_ready_i    ( dec_ready         ),
        .ic_valid_o     ( ic_valid          ),
        .ic_fetch_mask_o( ic_rsp.fetch_mask ),
        .ic_pc_o        ( ic_rsp.pc         ),
        .ic_act_mask_o  ( ic_rsp.act_mask   ),
        .ic_warp_id_o   ( ic_rsp.wid        ),
        .ic_subwarp_id_o( ic_rsp.subwarp_id ),
        .ic_inst_o      ( ic_rsp.enc_inst   )
    );

    assign ic_rsp.valid = ic_valid;

    // ########################################################################################
    // # Simulation Logic                                                                     #
    // ########################################################################################

    initial begin : simulation_logic
        int unsigned cycles, fetch_req_count, mem_req_count, dec_rsp_count, dec_inst_count;
        ic_rsp_t grsp, queued_rsp;
        logic match;

        cycles = 0;
        fetch_req_count = 0;
        mem_req_count = 0;
        dec_rsp_count = 0;
        dec_inst_count = 0;

        $timeformat(-9, 0, "ns", 12);
        // configure VCD dump
        $dumpfile("instruction_cache.vcd");
        $dumpvars();

        while (cycles < MaxSimCycles && dec_rsp_count < NumInsts) begin
            @(posedge clk);
            #AcqDelay;

            // Process fetch request
            if (fetch_req_valid && ic_ready) begin
                $display("Cycle %0d: Fetch Req PC: %0h, Warp ID: %0d, Act Mask: %b, Fetch Mask: %b",
                         cycles, fetch_req.pc, fetch_req.wid, fetch_req.act_mask,
                         fetch_req_fetch_mask);
                fetch_req_count++;
            end

            // Process memory request
            if (mem_req_valid && mem_ready) begin
                $display("Cycle %0d: Memory Request - Address: %0h", cycles, mem_req_addr
                    * (1 << CachelineIdxBits));
                mem_req_count++;
            end

            // Memory response
            if (mem_rsp_valid) begin
                $display("Cycle %0d: Memory Response - Data: %0h", cycles, mem_rsp);
            end

            // Process decoder response
            if ((|ic_valid) && dec_ready) begin
                $display("Cycle %0d: Decoder Response - Valid: %b, PC: %0h, Warp ID: %0d",
                            cycles, ic_valid, ic_rsp.pc, ic_rsp.wid);
                $display("Active Mask: %b, Fetch Mask: %b, Instruction: ",
                            ic_rsp.act_mask, ic_rsp.fetch_mask);
                for (int fidx = 0; fidx < FetchWidth; fidx++) begin
                    $display("[%d]: %0h", fidx, ic_rsp.enc_inst[fidx]);
                    if (ic_valid[fidx])
                        dec_inst_count++;
                end
                dec_rsp_count++;
            end

            if (golden_rsp.size() > 0 && i_ic_rsp_to_decoder.gen_queue.queue.size() > 0) begin
                // Check if the response matches the golden model
                grsp = golden_rsp.pop_front();
                queued_rsp = i_ic_rsp_to_decoder.gen_queue.queue.pop_front();

                match = (grsp.valid == queued_rsp.valid) &&
                        (grsp.fetch_mask == queued_rsp.fetch_mask) &&
                        (grsp.pc == queued_rsp.pc) &&
                        (grsp.wid == queued_rsp.wid) &&
                        (grsp.act_mask == queued_rsp.act_mask) &&
                        (grsp.enc_inst == queued_rsp.enc_inst) &&
                        (grsp.subwarp_id == queued_rsp.subwarp_id);

                assert(match) else begin
                    $display("Cycle %0d: Mismatch in decoder response", cycles);
                    $display("Expected: Valid: %b actual: %b", grsp.valid, queued_rsp.valid);
                    $display("Expected: Fetch Mask: %b actual: %b", grsp.fetch_mask,
                             queued_rsp.fetch_mask);
                    $display("Expected: PC: %0h actual: %0h", grsp.pc, queued_rsp.pc);
                    $display("Expected: Warp ID: %0d actual: %0d", grsp.wid, queued_rsp.wid);
                    $display("Expected: Subwarp ID: %0d actual: %0d",
                        grsp.subwarp_id, queued_rsp.subwarp_id);
                    $display("Expected: Active Mask: %b actual: %b",
                        grsp.act_mask, queued_rsp.act_mask);
                    for (int fidx = 0; fidx < FetchWidth; fidx++) begin
                        $display("Expected: Instruction [%0d]: %0h actual: %0h",
                            fidx, grsp.enc_inst[fidx], queued_rsp.enc_inst[fidx]);
                    end
                    $error("Decoder response does not match golden model");
                end
            end

            cycles++;
        end

        $dumpflush;

        assert(cycles < MaxSimCycles) else
            $error("Simulation exceeded maximum cycles: %0d", MaxSimCycles);

        assert(mem_req_count > 0) else
            $error("No memory requests generated");

        assert(dec_rsp_count == NumInsts) else
            $error("Not enough decoder responses: %0d, expected %0d", dec_rsp_count, NumInsts);

        assert(fetch_req_count >= NumInsts) else
            $error("Not enough fetch requests generated: %0d, expected at least %0d",
                fetch_req_count, NumInsts);

        $display("Simulation completed successfully after %0d cycles", cycles);
        $display("Sent %d responses to decoder, %d valid instructions", dec_rsp_count,
            dec_inst_count);
        $display("Average inst per response: %f", real'(dec_inst_count) / real'(dec_rsp_count));
        $finish;
    end : simulation_logic

endmodule : tb_instruction_cache
