// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Testbench for Register File Bank
module tb_register_file_bank #(
    // Simulation parameters
    parameter int unsigned MaxSimCycles     = 1000000,
    parameter int unsigned WatchdogTimeout  = 1000,
    parameter int unsigned MaxMstWaitCycles = 100,

    // Simulation time parameters
    parameter time         ClkPeriod = 10ns,
    parameter time         ApplDelay = 1ns,
    parameter time         AcqDelay  = 9ns,

    // Register file configuration
    parameter int unsigned NumRegisters = 256,
    parameter int unsigned DataWidth    = 32 - $clog2(NumRegisters),
    parameter bit          DualPort     = 1'b0
) ();
    typedef logic [$clog2(NumRegisters)-1:0] addr_t;
    typedef logic [DataWidth-1:0] data_t;

    typedef logic [$bits(addr_t)+$bits(data_t)-1:0] write_req_t;

    // #######################################################################################
    // # Signals                                                                           #
    // #######################################################################################

    // Clock and reset
    logic clk, rst_n;

    // Write port
    logic write_valid_mst, write_valid_sub, write_ready_mst, write_ready_sub;
    write_req_t write_req;
    addr_t write_addr;
    data_t write_data;

    // Read port
    logic read_valid, read_ready, read_out_valid;
    addr_t read_addr, read_out_addr;
    data_t read_out_data;

    // #######################################################################################
    // # DUT instantiation                                                                  #
    // #######################################################################################

    register_file_bank #(
        .DataWidth(DataWidth),
        .NumRegisters(NumRegisters),
        .DualPort(DualPort)
    ) dut (
        .clk_i ( clk   ),
        .rst_ni( rst_n ),

        .write_valid_i( write_valid_sub ),
        .write_ready_o( write_ready_sub ),
        .write_addr_i ( write_addr      ),
        .write_data_i ( write_data      ),

        .read_valid_i( read_valid ),
        .read_ready_o( read_ready ),
        .read_addr_i ( read_addr  ),

        .read_valid_o( read_out_valid ),
        .read_addr_o ( read_out_addr  ),
        .read_data_o ( read_out_data  )
    );

    // #######################################################################################
    // # Clock generation                                                                   #
    // #######################################################################################

    clk_rst_gen #(
        .ClkPeriod   ( ClkPeriod ),
        .RstClkCycles( 3         )
    ) i_clk_rst_gen (
        .clk_o ( clk   ),
        .rst_no( rst_n )
    );

    // #######################################################################################
    // # Stream Masters                                                                      #
    // #######################################################################################

    // Write port
    rand_stream_mst #(
        .data_t       ( write_req_t      ),
        .ApplDelay    ( ApplDelay        ),
        .AcqDelay     ( AcqDelay         ),
        .MinWaitCycles( 0                ),
        .MaxWaitCycles( MaxMstWaitCycles )
    ) i_write_port (
        .clk_i  ( clk             ),
        .rst_ni ( rst_n           ),
        .data_o ( write_req       ),
        .valid_o( write_valid_mst ),
        .ready_i( write_ready_mst )
    );

    assign write_addr = write_req[$bits(addr_t)-1:0];
    assign write_data = write_req[$bits(addr_t)+$bits(data_t)-1:$bits(addr_t)];

    // Read port
    rand_stream_mst #(
        .data_t       ( addr_t           ),
        .ApplDelay    ( ApplDelay        ),
        .AcqDelay     ( AcqDelay         ),
        .MinWaitCycles( 0                ),
        .MaxWaitCycles( MaxMstWaitCycles )
    ) i_read_port (
        .clk_i  ( clk         ),
        .rst_ni ( rst_n       ),
        .data_o ( read_addr   ),
        .valid_o( read_valid  ),
        .ready_i( read_ready  )
    );

    // Prevent write port from writing to the same address as the read port
    always_comb begin
        write_valid_sub = write_valid_mst;
        write_ready_mst = write_ready_sub;

        if (write_valid_mst && read_valid && (write_addr != read_addr)) begin
            write_valid_sub = 1'b0;
            write_ready_mst = 1'b0;
        end
    end

    // #######################################################################################
    // # Golden Model                                                                        #
    // #######################################################################################

    // Golden memory contents
    data_t [NumRegisters-1:0] golden_mem;

    // Golden read port
    logic  golden_read_valid;
    addr_t golden_read_addr;
    data_t golden_read_data;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            /* verilator lint_off WIDTHCONCAT */
            golden_mem <= '1;
            /* verilator lint_on WIDTHCONCAT */
        end else begin
            // Write handshake
            if (write_valid_sub && write_ready_sub)
                golden_mem[write_addr] <= write_data;

            // Read handshake
            if (read_valid && read_ready) begin
                golden_read_valid <= 1'b1;
                golden_read_addr  <= read_addr;
                golden_read_data  <= golden_mem[read_addr];
            end else begin
                golden_read_valid <= 1'b0;
            end
        end
    end

    // #######################################################################################
    // # Assertions and Watchdogs                                                            #
    // #######################################################################################

    // Read port watchdog
    stream_watchdog #(
        .NumCycles( WatchdogTimeout )
    ) i_read_watchdog (
        .clk_i   ( clk         ),
        .rst_ni  ( rst_n       ),
        .valid_i ( read_valid  ),
        .ready_i ( read_ready  )
    );

    // If we have a single port, then a read must stall if the write port is busy
    if (!DualPort) begin : gen_single_port_read_stall_assertion
        assert property (@(posedge clk) disable iff (!rst_n)
            read_valid && write_valid_sub |-> (!read_ready && write_ready_sub)
        ) else $error("Read port not stalled: read valid %b ready %b write valid %b ready %b",
            read_valid, read_ready, write_valid_sub, write_ready_sub);
    end : gen_single_port_read_stall_assertion

    // Write port watchdog
    stream_watchdog #(
        .NumCycles( WatchdogTimeout )
    ) i_write_watchdog (
        .clk_i   ( clk             ),
        .rst_ni  ( rst_n           ),
        .valid_i ( write_valid_sub ),
        .ready_i ( write_ready_sub )
    );

    // Writes should never stall
    assert property (@(posedge clk) disable iff (!rst_n)
        write_valid_sub |-> (write_ready_sub)
    ) else $error("Write port stalled: valid %b ready %b", write_valid_sub, write_ready_sub);

    // Check that the DUT's read data matches the golden model
    assert property (@(posedge clk) disable iff (!rst_n)
         (read_out_valid || golden_read_valid) -> (read_out_valid == golden_read_valid)
         && (read_out_data == golden_read_data)
         && (read_out_addr == golden_read_addr)
    ) else $error("Read mismatch: DUT read data %h addr %h, golden read data %h addr %h",
        read_out_data, read_out_addr, golden_read_data, golden_read_addr);

    // ########################################################################################
    // # Simulation timeout                                                                  #
    // ########################################################################################

    initial begin : simulation_timeout
        int unsigned cycles;
        int unsigned num_reads;
        int unsigned num_writes;

        cycles = 0;
        num_reads = 0;
        num_writes = 0;

        $display("Testbench for Register File Bank");
        $display(" with %0d ports, %0d registers, %0d bits per register", DualPort ? 2 : 1,
            NumRegisters, DataWidth);

        $display("Simulation started, running for %0d cycles", MaxSimCycles);

        while(cycles < MaxSimCycles) begin
            @(posedge clk);
            cycles++;
            if (read_valid && read_ready) begin
                num_reads++;
            end
            if (write_valid_sub && write_ready_sub) begin
                num_writes++;
            end
        end

        $display("Number of reads: %0d", num_reads);
        $display("Number of writes: %0d", num_writes);

        assert (num_reads > 0) else $fatal("No read transactions were performed");
        assert (num_writes > 0) else $fatal("No write transactions were performed");

        $display("Simulation ended after %0d cycles", cycles);
        $finish;
    end : simulation_timeout

endmodule : tb_register_file_bank
