// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Testbench for Coalesce Splitter
module tb_coalesce_splitter #(
    // Simulation parameters
    parameter int unsigned MaxSimCycles       = 100000,
    parameter int unsigned WatchdogTimeout    = 100,
    parameter int unsigned RequestsToCoalesce = 1000,
    parameter int unsigned MaxMstWaitCycles   = 10,
    parameter int unsigned MaxSubWaitCycles   = 10,

    // Simulation time parameters
    parameter time ClkPeriod = 10ns,
    parameter time ApplDelay = 1ns,
    parameter time AcqDelay  = 8ns,

    // Number of parallel requests, usually the warp width
    parameter int unsigned NumRequests = 4,
    // Memory Address width in bits
    parameter int unsigned AddressWidth = 8,
    // Memory Block size in bytes -> Memory request width
    parameter int unsigned BlockIdxBits = 4,
    // Width of the ID that is common for all sub-requests
    parameter int unsigned CommonReqIdWidth = 8,
    // Width of the data in a warp
    parameter int unsigned WarpDataWidth = 32,
    // Width of the write width
    parameter int unsigned WriteWidth = 32
) ();
    // #######################################################################################
    // # Local Parameters                                                                    #
    // #######################################################################################

    localparam int unsigned SubReqIdWidth = NumRequests > 1 ? $clog2(NumRequests) : 1;

    // #######################################################################################
    // # Type Definitions                                                                    #
    // #######################################################################################

    typedef logic         [              NumRequests-1:0] valid_mask_t;
    typedef logic         [             AddressWidth-1:0] addr_t;
    typedef addr_t        [              NumRequests-1:0] req_addr_t;
    typedef logic         [             BlockIdxBits-1:0] block_idx_t;
    typedef block_idx_t   [              NumRequests-1:0] block_offsets_t;
    typedef logic         [AddressWidth-BlockIdxBits-1:0] block_addr_t;
    typedef logic         [         CommonReqIdWidth-1:0] com_req_id_t;
    typedef logic         [            SubReqIdWidth-1:0] sub_req_id_t;
    typedef logic         [            WarpDataWidth-1:0] warp_data_t;
    typedef logic         [               WriteWidth-1:0] write_width_t;

    typedef struct packed {
        valid_mask_t  req_valid;
        logic         req_we;
        req_addr_t    req_addr;
        com_req_id_t  req_com_id;
        warp_data_t   req_wdata;
        write_width_t req_width;
    } req_t;

    typedef struct packed {
        block_addr_t    rsp_addr;
        block_offsets_t rsp_offsets;
        logic           rsp_we;
        com_req_id_t    rsp_com_id;
        sub_req_id_t    rsp_sub_id;
        warp_data_t     rsp_wdata;
        write_width_t   rsp_width;
    } rsp_t;

    typedef struct packed {
        int           thread_id;
        logic         we;
        block_addr_t  addr;
        block_idx_t   offset;
        com_req_id_t  com_req_id;
        sub_req_id_t  sub_req_id;
        warp_data_t   wdata;
        write_width_t width;
    } per_thread_rsp_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Clock and rest
    logic clk, rst_n;

    // Request
    logic req_valid, req_ready;
    req_t req;

    // Response
    valid_mask_t rsp_valid;
    logic rsp_ready;
    rsp_t rsp;

    // #######################################################################################
    // # Clock generation                                                                    #
    // #######################################################################################

    clk_rst_gen #(
        .ClkPeriod   ( ClkPeriod ),
        .RstClkCycles( 3         )
    ) i_clk_rst_gen (
        .clk_o ( clk   ),
        .rst_no( rst_n )
    );

    // #######################################################################################
    // # Request Master                                                                      #
    // #######################################################################################

    rand_stream_mst #(
        .data_t       ( req_t           ),
        .ApplDelay    ( ApplDelay        ),
        .AcqDelay     ( AcqDelay         ),
        .MinWaitCycles( 0                ),
        .MaxWaitCycles( MaxMstWaitCycles )
    ) i_req_mst (
        .clk_i  ( clk       ),
        .rst_ni ( rst_n     ),
        .valid_o( req_valid ),
        .ready_i( req_ready ),
        .data_o ( req       )
    );

    stream_watchdog #(
        .NumCycles( WatchdogTimeout )
    ) i_dispatcher_watchdog (
        .clk_i  ( clk       ),
        .rst_ni ( rst_n     ),
        .valid_i( req_valid ),
        .ready_i( req_ready )
    );

    // #######################################################################################
    // # Response Subordinate                                                                #
    // #######################################################################################

    rand_stream_slv #(
        .data_t       ( rsp_t            ),
        .ApplDelay    ( ApplDelay        ),
        .AcqDelay     ( AcqDelay         ),
        .MinWaitCycles( 1                ),
        .MaxWaitCycles( MaxSubWaitCycles ),
        .Enqueue      ( 1'b1             )
    ) i_result_sub (
        .clk_i  ( clk        ),
        .rst_ni ( rst_n      ),
        .data_i ( rsp        ),
        .valid_i( |rsp_valid ),
        .ready_o( rsp_ready  )
    );

    stream_watchdog #(
        .NumCycles( WatchdogTimeout )
    ) i_result_watchdog (
        .clk_i  ( clk        ),
        .rst_ni ( rst_n      ),
        .valid_i( |rsp_valid ),
        .ready_i( rsp_ready  )
    );

    // #######################################################################################
    // # DUT                                                                                 #
    // #######################################################################################

    coalesce_splitter #(
        .NumRequests     ( NumRequests      ),
        .AddressWidth    ( AddressWidth     ),
        .BlockIdxBits    ( BlockIdxBits     ),
        .CommonReqIdWidth( CommonReqIdWidth ),
        .warp_data_t     ( warp_data_t      ),
        .write_width_t   ( write_width_t    )
    ) i_coalesce_splitter (
        .clk_i ( clk   ),
        .rst_ni( rst_n ),

        .valid_i      ( req_valid      ),
        .ready_o      ( req_ready      ),
        .we_i         ( req.req_we     ),
        .req_id_i     ( req.req_com_id ),
        .addr_valid_i ( req.req_valid  ),
        .addr_i       ( req.req_addr   ),
        .wdata_i      ( req.req_wdata  ),
        .write_width_i( req.req_width  ),

        .req_ready_i      ( rsp_ready       ),
        .req_valid_o      ( rsp_valid       ),
        .req_we_o         ( rsp.rsp_we      ),
        .req_com_id_o     ( rsp.rsp_com_id  ),
        .req_sub_id_o     ( rsp.rsp_sub_id  ),
        .req_addr_o       ( rsp.rsp_addr    ),
        .req_offsets_o    ( rsp.rsp_offsets ),
        .req_wdata_o      ( rsp.rsp_wdata   ),
        .req_write_width_o( rsp.rsp_width   )
    );

    // ########################################################################################
    // # Check Logic                                                                          #
    // ########################################################################################

    per_thread_rsp_t dut_rsp [$];

    initial begin : capture_dut
        per_thread_rsp_t thread_rsp;
        while(1) begin
            @(posedge clk);
            #AcqDelay;
            if (rsp_ready && (|rsp_valid)) begin
                for (int i = 0; i < NumRequests; i++) begin
                    if (rsp_valid[i]) begin
                        thread_rsp            = '0;
                        thread_rsp.thread_id  = i;
                        thread_rsp.we         = rsp.rsp_we;
                        thread_rsp.addr       = rsp.rsp_addr;
                        thread_rsp.offset     = rsp.rsp_offsets[i];
                        thread_rsp.com_req_id = rsp.rsp_com_id;
                        thread_rsp.sub_req_id = rsp.rsp_sub_id;
                        thread_rsp.wdata      = rsp.rsp_wdata;
                        thread_rsp.width      = rsp.rsp_width;
                        dut_rsp.push_back(thread_rsp);

                        // $display("DUT: Thread %0d, Address %h, Offset %h",
                        //     thread_rsp.thread_id, thread_rsp.addr, thread_rsp.offset);
                    end
                end
            end
        end
    end : capture_dut

    per_thread_rsp_t golden_rsp [$];

    initial begin : golden_model
        int unsigned sub_req_id;
        per_thread_rsp_t thread_rsp;
        valid_mask_t valid;

        while(1) begin
            @(posedge clk);
            #AcqDelay;

            if (req_valid && req_ready) begin
                valid      = req.req_valid;
                sub_req_id = 0;
                for (int i = 0; i < NumRequests; i++) begin
                    // Skip inactive threads
                    if (!valid[i]) begin
                        continue;
                    end

                    thread_rsp            = '0;
                    thread_rsp.thread_id  = i;
                    thread_rsp.we         = req.req_we;
                    thread_rsp.addr       = req.req_addr[i][AddressWidth-1:BlockIdxBits];
                    thread_rsp.offset     = req.req_addr[i][BlockIdxBits-1:0];
                    thread_rsp.com_req_id = req.req_com_id;
                    thread_rsp.sub_req_id = sub_req_id[SubReqIdWidth-1:0];
                    thread_rsp.wdata      = req.req_wdata;
                    thread_rsp.width      = req.req_width;

                    // $display("Golden Model: Thread %0d, Address %h, Offset %h",
                    //     thread_rsp.thread_id, thread_rsp.addr, thread_rsp.offset);

                    golden_rsp.push_back(thread_rsp);
                    sub_req_id++; // New sub-request with new address

                    valid[i] = 0; // Mark as processed

                    // Search for other threads with the same address -> Part of same sub-request
                    for (int j = 0; j < NumRequests; j++) begin
                        if (i == j) begin
                            continue; // Skip self
                        end
                        if (valid[j] && (req.req_addr[i][AddressWidth-1:BlockIdxBits] ==
                                req.req_addr[j][AddressWidth-1:BlockIdxBits])) begin

                            thread_rsp.thread_id = j;
                            thread_rsp.offset    = req.req_addr[j][BlockIdxBits-1:0];

                            golden_rsp.push_back(thread_rsp);

                            valid[j] = 0; // Mark as processed
                        end
                    end
                end
            end
        end
    end : golden_model

    initial begin : compare_results
        per_thread_rsp_t dut_rsp_item, golden_rsp_item;

        while(1) begin
            @(posedge clk);
            #AcqDelay;

            if (dut_rsp.size() == 0 || golden_rsp.size() == 0) begin
                continue;
            end

            dut_rsp_item    = dut_rsp.pop_front();
            golden_rsp_item = golden_rsp.pop_front();

            assert (dut_rsp_item.thread_id == golden_rsp_item.thread_id)
                else $error("Thread ID mismatch: DUT %0d, Golden %0d", dut_rsp_item.thread_id,
                    golden_rsp_item.thread_id);

            assert (dut_rsp_item.we == golden_rsp_item.we)
                else $error("Write Enable mismatch: DUT %b, Golden %b", dut_rsp_item.we,
                    golden_rsp_item.we);

            assert (dut_rsp_item.addr == golden_rsp_item.addr)
                else $error("Address mismatch: DUT %h, Golden %h", dut_rsp_item.addr,
                    golden_rsp_item.addr);

            assert (dut_rsp_item.offset == golden_rsp_item.offset)
                else $error("Offset mismatch: DUT %h, Golden %h", dut_rsp_item.offset,
                    golden_rsp_item.offset);

            assert (dut_rsp_item.com_req_id == golden_rsp_item.com_req_id)
                else $error("Common Request ID mismatch: DUT %h, Golden %h",
                    dut_rsp_item.com_req_id, golden_rsp_item.com_req_id);

            assert (dut_rsp_item.sub_req_id == golden_rsp_item.sub_req_id)
                else $error("Sub Request ID mismatch: DUT %h, Golden %h", dut_rsp_item.sub_req_id,
                    golden_rsp_item.sub_req_id);

            assert (dut_rsp_item.wdata == golden_rsp_item.wdata)
                else $error("Wdata mismatch: DUT %h, Golden %h", dut_rsp_item.wdata,
                    golden_rsp_item.wdata);

            assert (dut_rsp_item.width == golden_rsp_item.width)
                else $error("Write Width mismatch: DUT %h, Golden %h", dut_rsp_item.width,
                    golden_rsp_item.width);
        end
    end : compare_results

    // ########################################################################################
    // # Simulation Logic                                                                     #
    // ########################################################################################

    initial begin : sim_logic
        int unsigned cycles, requests_issued, request_coalesced;

        cycles            = 0;
        requests_issued   = 0;
        request_coalesced = 0;

        $timeformat(-9, 0, "ns", 12);
        // configure VCD dump
        $dumpfile("coalesce_splitter.vcd");
        $dumpvars(1,i_coalesce_splitter);

        @(posedge clk);
        wait(!rst_n);

        $display("Starting simulation...");

        while (cycles < MaxSimCycles && requests_issued < RequestsToCoalesce) begin
            @(posedge clk);
            #AcqDelay;

            if (req_valid && req_ready) begin
                $display("Cycle %0d: New req: valid mask %b, addr %h, com id: %h", cycles,
                    req.req_valid, req.req_addr, req.req_com_id);
                requests_issued++;
            end

            if ((|rsp_valid) && rsp_ready) begin
                $display("Cycle %0d: Coalesced resp: valid mask %b, addr %h, com id: %h sub id: %h",
                    cycles, rsp_valid, rsp.rsp_addr, rsp.rsp_com_id, rsp.rsp_sub_id);
                for (int i = 0; i < NumRequests; i++) begin
                    if (rsp_valid[i]) begin
                        $display("  Offset %0d: %0h", i, rsp.rsp_offsets[i]);
                    end
                end
                request_coalesced++;
            end

            cycles++;
        end
        $dumpflush;

        $display("Simulation finished after %0d cycles.", cycles);
        $display("Total requests issued: %0d", requests_issued);
        $finish();
    end : sim_logic

endmodule : tb_coalesce_splitter
