// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Testbench for Load Store Unit
module tb_load_store_unit import bgpu_pkg::*; #(
    // Simulation parameters
    parameter int unsigned MaxSimCycles     = 100000,
    parameter int unsigned WatchdogTimeout  = 1000,
    parameter int unsigned InstsToComplete  = 2000,
    parameter int unsigned MaxMstWaitCycles = 0,
    parameter int unsigned MaxSubWaitCycles = 0,

    // Simulation time parameters
    parameter time ClkPeriod = 10ns,
    parameter time ApplDelay = 1ns,
    parameter time AcqDelay  = 8ns,

    /// Number of inflight instructions per warp
    parameter int unsigned NumTags = 8,
    /// Width of the Program Counter
    parameter int unsigned PcWidth = 32,
    /// Number of warps per compute unit
    parameter int unsigned NumWarps = 4,
    /// Number of threads per warp
    parameter int unsigned WarpWidth = 4,
    /// How many registers can each warp access as operand or destination
    parameter int unsigned RegIdxWidth = 32,
    /// How many operands each instruction can have
    parameter int unsigned OperandsPerInst = 2,
    /// Width of a singled register
    parameter int unsigned RegWidth = 32,

    // Memory Block size in bytes -> Memory request width
    parameter int unsigned BlockIdxBits = 4,
    // Memory Address width in bits
    parameter int unsigned AddressWidth = BlockIdxBits + 1,
    // Width of the id for requests queue
    parameter int unsigned OutstandingReqIdxWidth = 3
) ();
    // #######################################################################################
    // # Local Parameters                                                                    #
    // #######################################################################################

    localparam int unsigned TagWidth = $clog2(NumTags);
    localparam int unsigned WidWidth = NumWarps > 1 ? $clog2(NumWarps) : 1;
    localparam int unsigned NumRegistersPerWarp = 1 << RegIdxWidth;
    localparam int unsigned BlockWidth      = 1 << BlockIdxBits;
    localparam int unsigned BlockAddrWidth  = AddressWidth - BlockIdxBits;
    localparam int unsigned OutstandingReqs = 1 << OutstandingReqIdxWidth;
    localparam int unsigned ThreadIdxWidth  = WarpWidth > 1 ? $clog2(WarpWidth) : 1;

    // #######################################################################################
    // # Type Definitions                                                                    #
    // #######################################################################################

    typedef logic  [RegWidth * WarpWidth-1:0] warp_data_t;
    typedef logic  [         RegIdxWidth-1:0] reg_idx_t;
    typedef logic  [          BlockWidth-1:0] block_mask_t;
    typedef logic  [      BlockAddrWidth-1:0] block_addr_t;
    typedef logic  [                     7:0] byte_t;
    typedef byte_t [          BlockWidth-1:0] block_data_t;
    typedef logic  [        BlockIdxBits-1:0] block_idx_t;
    typedef logic  [           WarpWidth-1:0] act_mask_t;
    typedef logic  [OutstandingReqIdxWidth + ThreadIdxWidth-1:0] req_id_t;

    typedef logic [            WidWidth-1:0] wid_t;
    typedef logic [             PcWidth-1:0] pc_t;
    typedef logic [   TagWidth+WidWidth-1:0] iid_t;

    typedef struct packed {
        iid_t       tag;
        pc_t        pc;
        act_mask_t  active_mask;
        inst_t      inst;
        reg_idx_t   dst;
        warp_data_t [OperandsPerInst-1:0] src_data;
    } eu_req_t;

    typedef struct packed {
        iid_t       tag;
        reg_idx_t   dst;
        warp_data_t data;
    } eu_rsp_t;

    typedef struct packed {
        req_id_t     id;
        block_addr_t addr;
        block_mask_t we_mask;
        block_data_t wdata;
    } mem_req_t;

    typedef struct packed {
        req_id_t     id;
        block_data_t data;
    } mem_rsp_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    logic clk, rst_n;

    // Execution Unit Request
    logic    eu_req_valid, eu_req_ready;
    eu_req_t eu_req;

    // Execution Unit Response
    logic    eu_rsp_valid, eu_rsp_ready;
    eu_rsp_t eu_rsp;

    // Memory Request
    logic     mem_req_valid, mem_ready;
    mem_req_t mem_req;

    // Memory Response
    logic     mem_rsp_valid;
    mem_rsp_t mem_rsp;

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
    // # Issue Interface Master                                                              #
    // #######################################################################################

    int unsigned insts_issued;

    rand_stream_mst #(
        .data_t       ( eu_req_t         ),
        .ApplDelay    ( ApplDelay        ),
        .AcqDelay     ( AcqDelay         ),
        .MinWaitCycles( 0                ),
        .MaxWaitCycles( MaxMstWaitCycles )
    ) i_issue_mst (
        .clk_i  ( clk          ),
        .rst_ni ( rst_n        ),
        .valid_o( eu_req_valid ),
        .ready_i( eu_req_ready ),
        .data_o ( eu_req       )
    );

    stream_watchdog #(
        .NumCycles( WatchdogTimeout )
    ) i_dispatcher_watchdog (
        .clk_i  ( clk          ),
        .rst_ni ( rst_n        ),
        .valid_i( eu_req_valid ),
        .ready_i( eu_req_ready )
    );

    // #######################################################################################
    // # Result Interface                                                                    #
    // #######################################################################################

    rand_stream_slv #(
        .data_t       ( eu_rsp_t        ),
        .ApplDelay    ( ApplDelay        ),
        .AcqDelay     ( AcqDelay         ),
        .MinWaitCycles( 1                ),
        .MaxWaitCycles( MaxSubWaitCycles ),
        .Enqueue      ( 1'b1             )
    ) i_result_sub (
        .clk_i  ( clk          ),
        .rst_ni ( rst_n        ),
        .data_i ( eu_rsp       ),
        .valid_i( eu_rsp_valid ),
        .ready_o( eu_rsp_ready )
    );

    stream_watchdog #(
        .NumCycles( WatchdogTimeout )
    ) i_result_watchdog (
        .clk_i  ( clk          ),
        .rst_ni ( rst_n        ),
        .valid_i( eu_rsp_valid ),
        .ready_i( eu_rsp_ready )
    );

    // #######################################################################################
    // # Memory                                                                              #
    // #######################################################################################

    rand_stream_slv #(
        .data_t       ( mem_req_t        ),
        .ApplDelay    ( ApplDelay        ),
        .AcqDelay     ( AcqDelay         ),
        .MinWaitCycles( 1                ),
        .MaxWaitCycles( MaxSubWaitCycles ),
        .Enqueue      ( 1'b0             )
    ) i_mem_sub (
        .clk_i  ( clk           ),
        .rst_ni ( rst_n         ),
        .data_i ( mem_req       ),
        .valid_i( mem_req_valid ),
        .ready_o( mem_ready     )
    );

    stream_watchdog #(
        .NumCycles( WatchdogTimeout )
    ) i_eu_watchdog (
        .clk_i  ( clk           ),
        .rst_ni ( rst_n         ),
        .valid_i( mem_req_valid ),
        .ready_i( mem_ready     )
    );

    mem_rsp_t mem_responses [$];
    byte_t [(1 << BlockAddrWidth) * BlockWidth-1:0] mem_data;

    // Requests are handled in order as soon as the request is received.
    // It is then added to a response queue which is shuffled randomly
    initial begin : sim_mem_write
        mem_rsp_t rsp;

        // Initialize memory with some data
        for (int i = 0; i < (1 << BlockAddrWidth) * BlockWidth; i++) begin
            mem_data[i] = i[7:0];
        end

        while(1) begin
            @(posedge clk);
            #AcqDelay;

            if (mem_ready && mem_req_valid) begin
                rsp.id = mem_req.id;

                rsp.data = '0;
                if(mem_req.we_mask == '0) begin
                    $display("Memory Read Request: ID=%0h, Addr=%0h", mem_req.id, mem_req.addr);
                    for(int j = 0; j < BlockWidth; j++) begin
                        // Read data from the memory block
                        rsp.data[j] = mem_data[j + int'(mem_req.addr) * BlockWidth];
                        $display("Read data[%0d] = %h from address %h",
                                 j, rsp.data[j], int'(mem_req.addr) * BlockWidth + j);
                    end
                end else begin
                    // Write to memory
                    $display("Memory Write Request: ID=%0h, Addr=%0h, WE=%b, WData=%h",
                             mem_req.id, mem_req.addr, mem_req.we_mask, mem_req.wdata);
                    for(int j = 0; j < BlockWidth; j++) begin
                        if (mem_req.we_mask[j]) begin
                            // Write byte to memory
                            mem_data[j + int'(mem_req.addr) * BlockWidth] = mem_req.wdata[j];
                        end
                    end
                end

                // Check that no response with the same ID exists
                for (int i = 0; i < mem_responses.size(); i++) begin
                    assert(mem_responses[i].id != mem_req.id)
                    else $error("Memory response with ID %0h already exists in the queue!",
                        mem_req.id);
                end

                // Add response to the queue
                mem_responses.push_back(rsp);

            end
        end
    end : sim_mem_write

    initial begin : sim_mem_response
        int unsigned random_shuffle;

        while(1) begin
            @(posedge clk);
            #ApplDelay;
            mem_rsp_valid = 1'b0;
            random_shuffle = $urandom_range(0, 1);
            if (random_shuffle == 0)
                continue;
            if (mem_responses.size() > 0) begin
                // Shuffle the queue to simulate an out-of-order memory access
                random_shuffle = $urandom_range(0, mem_responses.size());
                while(random_shuffle > 0) begin
                    mem_responses.push_back(mem_responses.pop_front());
                    random_shuffle--;
                end

                // Perform the request
                mem_rsp_valid = 1'b1;
                mem_rsp = mem_responses.pop_front();
            end
        end
    end : sim_mem_response

    // #######################################################################################
    // # DUT                                                                                 #
    // #######################################################################################

    bgpu_pkg::lsu_subtype_e INSTS [6] = {
        LSU_LOAD_BYTE, LSU_LOAD_HALF, LSU_LOAD_WORD, LSU_STORE_BYTE, LSU_STORE_HALF, LSU_STORE_WORD
    };
    bgpu_pkg::lsu_subtype_e inst;
    assign inst = INSTS[eu_req.inst.subtype % 6];

    act_mask_t non_zero_mask;
    assign non_zero_mask = (eu_req.active_mask != '0) ? eu_req.active_mask : '1;

    load_store_unit #(
        .RegWidth ( RegWidth ),
        .WarpWidth ( WarpWidth ),
        .OperandsPerInst ( OperandsPerInst ),
        .RegIdxWidth  ( RegIdxWidth ),
        .iid_t        ( iid_t ),
        .AddressWidth ( AddressWidth ),
        .BlockIdxBits ( BlockIdxBits ),
        .OutstandingReqIdxWidth ( OutstandingReqIdxWidth )
    ) i_load_store_unit (
        .clk_i  ( clk   ),
        .rst_ni ( rst_n ),

        .mem_ready_i      ( mem_ready       ),
        .mem_req_valid_o  ( mem_req_valid   ),
        .mem_req_id_o     ( mem_req.id      ),
        .mem_req_addr_o   ( mem_req.addr    ),
        .mem_req_we_mask_o( mem_req.we_mask ),
        .mem_req_wdata_o  ( mem_req.wdata   ),

        .mem_rsp_valid_i( mem_rsp_valid ),
        .mem_rsp_id_i   ( mem_rsp.id    ),
        .mem_rsp_data_i ( mem_rsp.data  ),

        .eu_to_opc_ready_o   ( eu_req_ready    ),
        .opc_to_eu_valid_i   ( eu_req_valid    ),
        .opc_to_eu_tag_i     ( eu_req.tag      ),
        .opc_to_eu_act_mask_i( non_zero_mask   ),
        .opc_to_eu_inst_sub_i( inst            ),
        .opc_to_eu_dst_i     ( eu_req.dst      ),
        .opc_to_eu_operands_i( eu_req.src_data ),

        .rc_to_eu_ready_i ( eu_rsp_ready ),
        .eu_to_rc_valid_o ( eu_rsp_valid ),
        .eu_to_rc_tag_o   ( eu_rsp.tag   ),
        .eu_to_rc_dst_o   ( eu_rsp.dst   ),
        .eu_to_rc_data_o  ( eu_rsp.data  )
    );

    // ########################################################################################
    // # Golden Model                                                                         #
    // ########################################################################################

    eu_rsp_t golden_responses [$];
    block_data_t [(1 << BlockAddrWidth)-1:0] golden_mem;

    initial begin : golden_model
        eu_rsp_t rsp;
        int unsigned wbyte, size, block_addr, block_offset;

        // Initialize golden memory with some data
        for(int i = 0; i < (1 << BlockAddrWidth); i++) begin
            for(int j = 0; j < BlockWidth; j++) begin
                wbyte = i * BlockWidth + j;
                golden_mem[i][j] = wbyte[7:0];
            end
        end

        while(1) begin
            @(posedge clk);
            #AcqDelay;

            if (!(eu_req_valid && eu_req_ready)) begin
                // No valid request, skip this cycle
                continue;
            end

            // Build response
            rsp.tag = eu_req.tag;
            rsp.dst = eu_req.dst;
            rsp.data = '0;

            $display("Golden Model: Req: Tag=%0d, PC=%0h, Active Mask=%b, Inst=%0h, Dst=%0d",
                     rsp.tag, eu_req.pc, non_zero_mask, eu_req.inst.subtype, rsp.dst);

            assert(non_zero_mask != '0) else $error("Golden Model: Active mask is zero!");

            // Overlapping store data get OR-ed together -> store 0 first
            for(int thread = 0; thread < WarpWidth; thread++) begin
                if (!non_zero_mask[thread]) begin
                    continue; // Skip inactive threads
                end
                if (inst inside `INST_STORE) begin
                    if (inst == LSU_STORE_BYTE) begin
                        size = 1;
                    end else if (inst == LSU_STORE_HALF) begin
                        size = 2;
                    end else if (inst == LSU_STORE_WORD) begin
                        size = 4;
                    end else begin
                        $error("Golden Model: Unsupported store instruction %0h", inst);
                    end
                    block_addr = int'(eu_req.src_data[0][thread * RegWidth +: AddressWidth])
                        / BlockWidth;
                    block_offset = int'(eu_req.src_data[0][thread * RegWidth +: AddressWidth])
                        % BlockWidth;
                    for(int i = 0; (i < RegWidth / 8) && (i < size); i++) begin
                        // Check that we're not storing outside of a block
                        if(block_offset == BlockWidth) begin
                            break;
                        end
                        // Write zero to golden memory
                        golden_mem[block_addr][block_offset] = 0;

                        block_offset++;
                    end
                end
            end

            for(int thread = 0; thread < WarpWidth; thread++) begin
                if (!non_zero_mask[thread]) begin
                    continue; // Skip inactive threads
                end
                if (inst inside `INST_LOAD) begin
                    if (inst == LSU_LOAD_BYTE) begin
                        size = 1;
                    end else if (inst == LSU_LOAD_HALF) begin
                        size = 2;
                    end else if (inst == LSU_LOAD_WORD) begin
                        size = 4;
                    end else begin
                        $error("Golden Model: Unsupported load instruction %0h", inst);
                    end
                    $display("Golden Model: Thread %0d is performing a LOAD operation of size",
                        thread, size);
                    block_addr = int'(eu_req.src_data[0][thread * RegWidth +: AddressWidth])
                        / BlockWidth;
                    block_offset = int'(eu_req.src_data[0][thread * RegWidth +: AddressWidth])
                        % BlockWidth;
                    for(int i = 0; (i < RegWidth / 8) && (i < size); i++) begin
                        // Check that we're not reading outside of a block
                        if(block_offset >= BlockWidth) begin
                            break;
                        end
                        // Read byte from golden memory
                        rsp.data[thread * RegWidth + i * 8 +: 8] =
                            golden_mem[block_addr][block_offset];

                        $display("Golden Model: Thread %0d, Block Addr=%0d, Offset=%0d, Data=%h",
                                 thread, block_addr, block_offset, rsp.data[thread * RegWidth
                                 + i * 8 +: 8]);

                        block_offset++;
                    end
                end else begin
                    if (inst == LSU_STORE_BYTE) begin
                        size = 1;
                    end else if (inst == LSU_STORE_HALF) begin
                        size = 2;
                    end else if (inst == LSU_STORE_WORD) begin
                        size = 4;
                    end else begin
                        $error("Golden Model: Unsupported store instruction %0h", inst);
                    end
                    $display("Golden Model: Thread %0d is performing a STORE operation of size",
                        thread, size);
                    block_addr = int'(eu_req.src_data[0][thread * RegWidth +: AddressWidth])
                        / BlockWidth;
                    block_offset = int'(eu_req.src_data[0][thread * RegWidth +: AddressWidth])
                        % BlockWidth;
                    for(int i = 0; (i < RegWidth / 8) && (i < size); i++) begin
                        // Check that we're not storing outside of a block
                        if(block_offset == BlockWidth) begin
                            break;
                        end
                        // Write byte to golden memory -> OR data together
                        golden_mem[block_addr][block_offset] = golden_mem[block_addr][block_offset]
                            | eu_req.src_data[1][thread * RegWidth + i * 8 +: 8];

                        $display("Golden Model: Thread %0d, Block Addr=%0d, Offset=%0d, Data=%h",
                                 thread, block_addr, block_offset,
                                 golden_mem[block_addr][block_offset]);

                        block_offset++;
                    end
                end
            end
            $display("Golden Model: Response built: Tag=%0d, Dst=%0d, Data=%h",
                     rsp.tag, rsp.dst, rsp.data);

            // Add to golden response queue
            golden_responses.push_back(rsp);
            rsp = golden_responses[golden_responses.size() - 1];
            $display("Golden Model: Response built: Tag=%0d, Dst=%0d, Data=%h",
                     rsp.tag, rsp.dst, rsp.data);
        end
    end : golden_model

    // ########################################################################################
    // # Assertions                                                                           #
    // ########################################################################################

    initial begin : check_result
        logic found;
        eu_rsp_t golden_rsp, dut_rsp;

        while(1) begin
            @(posedge clk);

            if (i_result_sub.gen_queue.queue.size() == 0) begin
                continue; // No results to check
            end

            dut_rsp = i_result_sub.gen_queue.queue.pop_front();

            $display("Checking response: Tag=%0d, Dst=%0d, Data=%h",
                     dut_rsp.tag, dut_rsp.dst, dut_rsp.data);

            found = 1'b0;
            for (int i = 0; i < golden_responses.size(); i++) begin
                golden_rsp = golden_responses[i];
                if (dut_rsp.tag == golden_rsp.tag && dut_rsp.dst == golden_rsp.dst) begin
                    $display("Found possible golden response: Tag=%0d, Dst=%0d, Data=%h",
                             golden_rsp.tag, golden_rsp.dst, golden_rsp.data);
                    if (dut_rsp.data == golden_rsp.data) begin
                        found = 1'b1;
                        // Remove from golden responses to avoid duplicates
                        golden_responses.delete(i);
                        break;
                    end
                    assert(dut_rsp.data == golden_rsp.data) else begin
                        $warning("Data mismatch: DUT=%h, Golden=%h", dut_rsp.data, golden_rsp.data);
                        $display("Might need to increase the RegIdxWidth to have more unique",
                            " requests!");
                        $display("Available golden responses:");
                        for (int i = 0; i < golden_responses.size(); i++) begin
                            golden_rsp = golden_responses[i];
                            $display("\tTag=%0d, Dst=%0d, Data=%h", golden_rsp.tag, golden_rsp.dst,
                                golden_rsp.data);
                        end
                        $error();
                    end
                end
            end

            assert(found) else begin
                $warning("No matching golden rsp found for DUT response: Tag=%0d, Dst=%0d, Data=%h",
                       dut_rsp.tag, dut_rsp.dst, dut_rsp.data);

                $display("Available golden responses:");
                for (int i = 0; i < golden_responses.size(); i++) begin
                    golden_rsp = golden_responses[i];
                    $display("\tTag=%0d, Dst=%0d, Data=%h", golden_rsp.tag, golden_rsp.dst,
                        golden_rsp.data);
                end
                $error();
            end
        end
    end : check_result

    // ########################################################################################
    // # Simulation Logic                                                                     #
    // ########################################################################################

    initial begin : sim_logic
        int unsigned cycles, insts_completed, occupancy;

        cycles = 0;
        insts_issued = 0;
        insts_completed = 0;
        occupancy = 0;

        $timeformat(-9, 0, "ns", 12);
        // configure VCD dump
        $dumpfile("load_store_unit.vcd");
        $dumpvars(1,i_register_opc_stage);

        @(posedge clk);
        wait(!rst_n);

        $display("Starting simulation...");

        while (cycles < MaxSimCycles && insts_completed < InstsToComplete) begin
            @(posedge clk);
            #AcqDelay;
            #1ns;

            // Count how many bits in i_load_store_unit.buffer_valid_q are set
            for(int i = 0; i < OutstandingReqs; i++) begin
                if(i_load_store_unit.buffer_valid_q[i]) begin
                    occupancy++;
                end
            end


            if (eu_req_valid && eu_req_ready) begin
                // Log issued instruction
                insts_issued++;
                $display("Cycle %0d", cycles);
                $display("\tIssued instruction: Tag=%0d, PC=%0h, Active Mask=%b, Inst=%0h, Dst=%0d",
                         eu_req.tag, eu_req.pc, non_zero_mask, eu_req.inst.subtype,
                         eu_req.dst);
                for (int thread = 0; thread < WarpWidth; thread++) begin
                    if (non_zero_mask[thread]) begin
                        $display("\tThread %0d, Addr=%h Data=%h",
                                 thread, eu_req.src_data[0][thread * RegWidth +: RegWidth],
                                 eu_req.src_data[1][thread * RegWidth +: RegWidth]);
                    end
                end
            end

            if (mem_req_valid && mem_ready) begin
                // Log memory request
                $display("Cycle %0d", cycles);
                $display("\tMemory Request: ID=%0h, Addr=%0h, WE=%b, WData=%h",
                         mem_req.id, mem_req.addr, mem_req.we_mask, mem_req.wdata);
            end

            if (mem_rsp_valid) begin
                // Log memory response
                $display("Cycle %0d", cycles);
                $display("\tMemory Response: ID=%0h, Data=%h", mem_rsp.id, mem_rsp.data);
            end

            // Check if we have completed the required number of instructions
            if (eu_rsp_valid && eu_rsp_ready) begin
                insts_completed++;
                $display("Cycle %0d", cycles);
                $display("\tCompleted instruction: Tag=%0d, Dst=%0d, Data=%h",
                         eu_rsp.tag, eu_rsp.dst, eu_rsp.data);
                if (cycles >= InstsToComplete) begin
                    $display("Completed %0d instructions, stopping simulation.", InstsToComplete);
                end
            end

            cycles++;
        end
        $dumpflush;

        $display("Finished after %0d cycles, %0d instructions completed.", cycles, insts_completed);
        $display("Issued %0d instructions.", insts_issued);
        $display("Occupancy of the request buffer: %0d/%0d (%0.2f)",
                 occupancy, cycles, occupancy / cycles);
        $finish();
    end : sim_logic

endmodule : tb_load_store_unit
