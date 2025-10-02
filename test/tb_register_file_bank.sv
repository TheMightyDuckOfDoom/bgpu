// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Testbench for Register File Bank
module tb_register_file_bank #(
    // Simulation parameters
    parameter int unsigned MaxSimCycles     = 1000000,
    parameter int unsigned WatchdogTimeout  = 1000,
    parameter int unsigned MaxMstWaitCycles = 10,

    // Simulation time parameters
    parameter time         ClkPeriod = 10ns,
    parameter time         ApplDelay = 1ns,
    parameter time         AcqDelay  = 9ns,

    // Register file configuration
    parameter int unsigned NumRegisters  = 1024,
    parameter int unsigned WarpWidth     = 4,
    parameter int unsigned RegisterWidth = 32,
    parameter int unsigned TagWidth      = 8,
    parameter bit          DualPort      = 1'b0
) ();
    // #######################################################################################
    // # Type definitions                                                                    #
    // #######################################################################################

    typedef logic  [$clog2(NumRegisters)-1:0] addr_t;
    typedef logic  [       RegisterWidth-1:0] data_t;
    typedef data_t [           WarpWidth-1:0] warp_data_t;
    typedef logic  [            TagWidth-1:0] tag_t;
    typedef logic  [           WarpWidth-1:0] we_mask_t;

    typedef struct packed {
        addr_t addr;
        tag_t  tag;
    } read_req_t;

    typedef struct packed {
        addr_t addr;
        warp_data_t data;
        we_mask_t we_mask;
    } write_req_t;

    localparam addr_t MaxAddr = NumRegisters[$clog2(NumRegisters)-1:0] - 'd1;

    // #######################################################################################
    // # Signals                                                                           #
    // #######################################################################################

    // Clock and reset
    logic clk, rst_n;

    // Write port
    logic write_valid_mst, write_valid_sub, write_ready_mst, write_ready_sub;
    write_req_t write_req;
    addr_t write_addr;
    warp_data_t write_data;

    // Read port
    logic read_valid, read_ready, read_out_valid;
    read_req_t read_req;
    addr_t read_addr;
    tag_t read_tag, read_out_tag;
    warp_data_t read_out_data;

    // #######################################################################################
    // # DUT instantiation                                                                  #
    // #######################################################################################

    register_file_bank #(
        .RegisterWidth( RegisterWidth ),
        .WarpWidth    ( WarpWidth     ),
        .NumRegisters ( NumRegisters  ),
        .DualPort     ( DualPort      ),
        .tag_t        ( tag_t         )
    ) i_register_file_bank (
        .clk_i ( clk   ),
        .rst_ni( rst_n ),

        .write_valid_i( write_valid_sub   ),
        .write_ready_o( write_ready_sub   ),
        .write_mask_i ( write_req.we_mask ),
        .write_addr_i ( write_addr        ),
        .write_data_i ( write_data        ),

        .read_valid_i( read_valid ),
        .read_ready_o( read_ready ),
        .read_addr_i ( read_addr  ),
        .read_tag_i  ( read_tag   ),

        .read_valid_o( read_out_valid ),
        .read_tag_o  ( read_out_tag   ),
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

    always_comb begin : gen_write_addr
        write_addr = write_req.addr;
        /* verilator lint_off CMPCONST */
        if (write_addr > MaxAddr) begin
        /* verilator lint_on CMPCONST */
            write_addr = write_addr % MaxAddr;
        end
    end : gen_write_addr

    assign write_data = write_req.data;

    // Read port
    rand_stream_mst #(
        .data_t       ( read_req_t       ),
        .ApplDelay    ( ApplDelay        ),
        .AcqDelay     ( AcqDelay         ),
        .MinWaitCycles( 0                ),
        .MaxWaitCycles( MaxMstWaitCycles )
    ) i_read_port (
        .clk_i  ( clk        ),
        .rst_ni ( rst_n      ),
        .data_o ( read_req   ),
        .valid_o( read_valid ),
        .ready_i( read_ready )
    );

    always_comb begin : gen_read_addr
        read_addr = read_req.addr;
        /* verilator lint_off CMPCONST */
        if (read_addr > MaxAddr) begin
        /* verilator lint_on CMPCONST */
            read_addr = read_addr % MaxAddr;
        end
    end : gen_read_addr

    assign read_tag = read_req.tag;

    // Prevent write port from writing to the same address as the read port
    always_comb begin
        write_valid_sub = write_valid_mst;
        write_ready_mst = write_ready_sub;

        if (write_valid_mst && read_valid && (write_addr == read_addr)) begin
            write_valid_sub = 1'b0;
            write_ready_mst = 1'b0;
        end
    end

    // #######################################################################################
    // # Golden Model                                                                        #
    // #######################################################################################

    // Golden memory contents
    warp_data_t [NumRegisters-1:0] golden_mem;

    // Golden read port
    logic       golden_read_valid;
    addr_t      golden_read_addr;
    warp_data_t golden_read_data;
    tag_t       golden_read_tag;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            /* verilator lint_off WIDTHCONCAT */
            golden_mem <= '0;
            /* verilator lint_on WIDTHCONCAT */
        end else begin
            // Write handshake
            if (write_valid_sub && write_ready_sub)
                for (int unsigned i = 0; i < WarpWidth; i++) begin
                    if (write_req.we_mask[i])
                        golden_mem[write_addr][i] <= write_data[i];
                end

            // Read handshake
            if (read_valid && read_ready) begin
                golden_read_valid <= 1'b1;
                golden_read_addr  <= read_addr;
                golden_read_data  <= golden_mem[read_addr];
                golden_read_tag   <= read_tag;
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

    // Check read valids
    assert property (@(posedge clk) disable iff (!rst_n)
        (read_out_valid || golden_read_valid) |-> (read_out_valid == golden_read_valid)
    ) else $error("Read valid mismatch for address %d: DUT %b, Golden %b",
            golden_read_addr, read_out_valid, golden_read_valid);

    // Check read tags
    assert property (@(posedge clk) disable iff (!rst_n)
        (read_out_valid || golden_read_valid) |-> (read_out_tag == golden_read_tag)
    ) else $error("Read tag mismatch for address %d: DUT %b, Golden %b",
            golden_read_addr, read_out_tag, golden_read_tag);

    // Check read data
    assert property (@(posedge clk) disable iff (!rst_n)
        (read_out_valid || golden_read_valid) |-> (read_out_data == golden_read_data)
    ) else $error("Read data mismatch for address %d: DUT %h, Golden %h",
            golden_read_addr, read_out_data, golden_read_data);

    if (!DualPort) begin : gen_single_port_read_write_assertions
        assert property (@(posedge clk) disable iff (!rst_n)
            (read_valid && read_ready) && (write_valid_sub && write_ready_mst)
            |-> (read_addr != write_addr)
        ) else $error("Read and write ports access the same address: read addr %0h, write addr %0h",
                read_addr, write_addr);
    end : gen_single_port_read_write_assertions

    // ########################################################################################
    // # Simulation timeout                                                                   #
    // ########################################################################################

    initial begin : simulation_timeout
        int unsigned cycles;
        int unsigned num_reads;
        int unsigned num_writes;
        int unsigned num_write_data_non_zero;

        cycles = 0;
        num_reads = 0;
        num_writes = 0;
        num_write_data_non_zero = 0;

        $display("Testbench for Register File Bank");
        $display(" with %0d ports, %0d registers, %0d bits per register", DualPort ? 2 : 1,
            NumRegisters, RegisterWidth);

        $timeformat(-9, 0, "ns", 12);
        // configure VCD dump
        $dumpfile("register_file_bank.vcd");
        $dumpvars();
        $display("Simulation started, running for %0d cycles", MaxSimCycles);

        while(cycles < MaxSimCycles) begin
            @(posedge clk);
            cycles++;
            if (read_valid && read_ready) begin
                num_reads++;
            end
            if (write_valid_sub && write_ready_sub) begin
                num_writes++;
                if (write_data != '0) begin
                    num_write_data_non_zero++;
                end
            end
        end

        $dumpflush;

        $display("Number of reads: %0d", num_reads);
        $display("Number of writes: %0d", num_writes);

        assert (num_reads > 0) else $error("No read transactions were performed");
        assert (num_writes > 0) else $error("No write transactions were performed");
        assert (num_write_data_non_zero > 0) else $error("No non-zero write data was written");

        $display("Simulation ended after %0d cycles", cycles);
        $finish;
    end : simulation_timeout

endmodule : tb_register_file_bank
