// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Testbench for Thread Dispatcher
module tb_thread_dispatcher #(
    /// Width of the Program Counter
    parameter int unsigned PcWidth = 16,
    // Memory Address width in bits
    parameter int unsigned AddressWidth = 32,
    // How many bits are used to index thread blocks inside a thread group?
    parameter int unsigned TblockIdxBits = 5,
    // How many bits are used to identify a thread group?
    parameter int unsigned TgroupIdBits = 8,
    /// Number of threads per warp
    parameter int unsigned WarpWidth = 4,

    // Simulation parameters
    parameter int unsigned RequestsToDispatch = 1000,
    parameter int unsigned WatchdogTimeout    = 10 * (1 << TblockIdxBits),
    parameter int unsigned MaxMstWaitCycles   = 0,
    parameter int unsigned MaxSubWaitCycles   = 1,

    // Simulation time parameters
    parameter time ClkPeriod = 10ns,
    parameter time ApplDelay = 1ns,
    parameter time AcqDelay  = 8ns

) ();

    // #######################################################################################
    // # Local Parameters                                                                    #
    // #######################################################################################

    localparam int unsigned ThreadIdxBits  = WarpWidth > 1 ? $clog2(WarpWidth) : 1;
    localparam int unsigned TblockSizeBits = TblockIdxBits + 1;

    // #######################################################################################
    // # Type Definitions                                                                    #
    // #######################################################################################

    typedef logic [       PcWidth-1:0] pc_t;
    typedef logic [  AddressWidth-1:0] addr_t;
    typedef logic [ TblockIdxBits-1:0] tblock_idx_t;
    typedef logic [  TgroupIdBits-1:0] tgroup_id_t;
    typedef logic [TblockSizeBits-1:0] tblock_size_t;

    typedef struct packed {
        pc_t          pc;
        addr_t        dp_addr;
        tblock_size_t tblock_size;
        tblock_idx_t  number_of_tblocks;
        tgroup_id_t   tgroup_id;
    } req_t;

    typedef struct packed {
        pc_t          pc;
        addr_t        dp_addr;
        tblock_size_t tblock_size;
        tblock_idx_t  tblock_idx;
        tgroup_id_t   tgroup_id;
    } warp_req_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Clock and reset
    logic clk, rst_n;

    // Inputs
    logic start, ready;
    req_t req;

    // Outputs
    logic allocate_warp, warp_free;
    warp_req_t warp_req;

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
    // # DUT Instantiation                                                                   #
    // #######################################################################################

    thread_dispatcher #(
        .PcWidth       ( PcWidth        ),
        .AddressWidth  ( AddressWidth   ),
        .TblockIdxBits ( TblockIdxBits  ),
        .TgroupIdBits  ( TgroupIdBits   ),
        .TblockSizeBits( TblockSizeBits )
    ) i_thread_dispatcher (
        .clk_i ( clk   ),
        .rst_ni( rst_n ),

        .ready_o            ( ready                 ),
        .start_i            ( start                 ),
        .pc_i               ( req.pc                ),
        .dp_addr_i          ( req.dp_addr           ),
        .number_of_tblocks_i( req.number_of_tblocks ),
        .tblock_size_i      ( req.tblock_size       ),
        .tgroup_id_i        ( req.tgroup_id         ),

        .warp_free_i           ( warp_free            ),
        .allocate_warp_o       ( allocate_warp        ),
        .allocate_pc_o         ( warp_req.pc          ),
        .allocate_dp_addr_o    ( warp_req.dp_addr     ),
        .allocate_tblock_size_o( warp_req.tblock_size ),
        .allocate_tblock_idx_o ( warp_req.tblock_idx  ),
        .allocate_tgroup_id_o  ( warp_req.tgroup_id   ),

        .dispatched_tblocks_o()
    );

    // #######################################################################################
    // # Request Interface Master                                                            #
    // #######################################################################################

    rand_stream_mst #(
        .data_t       ( req_t            ),
        .ApplDelay    ( ApplDelay        ),
        .AcqDelay     ( AcqDelay         ),
        .MinWaitCycles( 0                ),
        .MaxWaitCycles( MaxMstWaitCycles )
    ) i_request_mst (
        .clk_i  ( clk   ),
        .rst_ni ( rst_n ),
        .valid_o( start ),
        .ready_i( ready ),
        .data_o ( req   )
    );

    stream_watchdog #(
        .NumCycles( WatchdogTimeout )
    ) i_request_timeout (
        .clk_i  ( clk   ),
        .rst_ni ( rst_n ),
        .valid_i( start ),
        .ready_i( ready )
    );

    // #######################################################################################
    // # Allocate Interface                                                                  #
    // #######################################################################################

    rand_stream_slv #(
        .data_t       ( warp_req_t       ),
        .ApplDelay    ( ApplDelay        ),
        .AcqDelay     ( AcqDelay         ),
        .MinWaitCycles( 1                ),
        .MaxWaitCycles( MaxSubWaitCycles ),
        .Enqueue      ( 1'b1             )
    ) i_allocate_sub (
        .clk_i  ( clk           ),
        .rst_ni ( rst_n         ),
        .data_i ( warp_req      ),
        .valid_i( allocate_warp ),
        .ready_o( warp_free     )
    );

    stream_watchdog #(
        .NumCycles( WatchdogTimeout )
    ) i_allocate_timeout (
        .clk_i  ( clk           ),
        .rst_ni ( rst_n         ),
        .valid_i( allocate_warp ),
        .ready_i( warp_free     )
    );

    // #######################################################################################
    // # Golden Model                                                                        #
    // #######################################################################################

    warp_req_t golden_requests [$];

    initial begin : golden_model
        warp_req_t golden_req;

        while (1) begin : golden_loop
            @(posedge clk);
            #AcqDelay;

            if (start && ready) begin : new_request
                golden_req.pc          = req.pc;
                golden_req.dp_addr     = req.dp_addr;
                golden_req.tblock_size = req.tblock_size;
                golden_req.tgroup_id   = req.tgroup_id;

                for (int i = 0; i < req.number_of_tblocks; i++) begin : tblock_loop
                    golden_req.tblock_idx = tblock_idx_t'(i);

                    // Store the request
                    golden_requests.push_back(golden_req);
                end : tblock_loop
            end : new_request
        end : golden_loop
    end : golden_model

    // #######################################################################################
    // # Testbench logic                                                                     #
    // #######################################################################################

    initial begin : compare_golden_model_dut
        warp_req_t dut_warp_req;
        warp_req_t golden_warp_req;

        while (1) begin : compare_loop
            @(posedge clk);

            if (golden_requests.size() == 0) continue;
            if (i_allocate_sub.gen_queue.queue.size() == 0) continue;

            golden_warp_req = golden_requests.pop_front();
            dut_warp_req    = i_allocate_sub.gen_queue.queue.pop_front();

            if (dut_warp_req != golden_warp_req) begin : mismatch
                $display("Mismatch in warp request!");
                $display("DUT: PC = %0h, DP_ADDR = %0h, TBLOCK_IDX = %0d, TGROUP_ID = %0h",
                    dut_warp_req.pc, dut_warp_req.dp_addr, dut_warp_req.tblock_idx,
                    dut_warp_req.tgroup_id);
                $display("TBLOCK_SIZE = %0d", dut_warp_req.tblock_size);
                $display("GOLDEN: PC = %0h, DP_ADDR = %0h, TBLOCK_IDX = %0d, TGROUP_ID = %0h",
                    golden_warp_req.pc, golden_warp_req.dp_addr, golden_warp_req.tblock_idx,
                    golden_warp_req.tgroup_id);
                $display("TBLOCK_SIZE = %0d", golden_warp_req.tblock_size);
                $error("Mismatch!");
            end : mismatch
        end
    end : compare_golden_model_dut

    initial begin : tb_main
        int unsigned dispatched_requests;
        dispatched_requests = 0;

        $timeformat(-9, 0, "ns", 12);
        // configure VCD dump
        $dumpfile("thread_dispatcher.vcd");
        $dumpvars();

        @(posedge clk);
        wait(!rst_n);

        $display("Starting simulation...");

        while (dispatched_requests < RequestsToDispatch) begin : dispatch_loop
            @(posedge clk);
            #AcqDelay;

            if (start && ready) begin : new_request
                $display("New request: PC = %0h, DP_ADDR = %0h, TGROUP_ID = %0h, TBLOCKS = %0d",
                    req.pc, req.dp_addr, req.tgroup_id, req.number_of_tblocks);
                dispatched_requests++;
            end : new_request

            if (allocate_warp && warp_free) begin : warp_allocated
                $display("Allocated: PC = %0h, DP_ADDR = %0h, TBLOCK_IDX = %0d, TGROUP_ID = %0h",
                    warp_req.pc, warp_req.dp_addr, warp_req.tblock_idx, warp_req.tgroup_id);
            end : warp_allocated
        end : dispatch_loop

        $display("Dispatched %0d requests", dispatched_requests);

        // Wait for all requests to be processed
        wait (golden_requests.size() == 0);
        @(posedge clk);

        // Finish the simulation
        $display("Finished!");
        $finish();
    end : tb_main

endmodule : tb_thread_dispatcher
