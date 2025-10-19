// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Testbench for Compute Unit
module tb_compute_unit import bgpu_pkg::*; #(
    /// Number of instructions that can write back simultaneously
    parameter int unsigned WritebackWidth = 1,
    /// Width of the Program Counter
    parameter int unsigned PcWidth = 16,
    /// Number of warps
    parameter int unsigned NumWarps = 8,
    /// Number of threads per warp
    parameter int unsigned WarpWidth = 4,
    /// Number of inflight instructions per warp
    parameter int unsigned InflightInstrPerWarp = 4,
    /// Number of banks in the register file
    parameter int unsigned NumBanks = 4,
    /// Number of operand collectors
    parameter int unsigned NumOperandCollectors = 6,
    /// How many operands can each instruction have
    parameter int unsigned OperandsPerInst = 2,
    /// How many bits are used to index a register
    parameter int unsigned RegIdxWidth = 8,
    /// Width of a register
    parameter int unsigned RegWidth = 32,
    // Memory Block size in bytes -> Memory request width
    parameter int unsigned BlockIdxBits = 4,
    /// Width of a memory address
    parameter int unsigned AddressWidth = 32,
    // Width of the id for requests queue
    parameter int unsigned OutstandingReqIdxWidth = 3,
    // Number of cache lines in the instruction cache
    parameter int unsigned NumIClines = 8,
    // Number of bits for the instruction cache line index
    parameter int unsigned IClineIdxBits = 2,
    // How many bits are used to index thread blocks inside a thread group?
    parameter int unsigned TblockIdxBits = 8,
    // How many bits are used to identify a thread group?
    parameter int unsigned TgroupIdBits = 8,

    // Force instructions to execute in-order
    parameter bit InorderExecution = 1'b0,

    parameter int unsigned SimMemBlocks = 65,

    parameter int unsigned TblocksToLaunch = 33,

    parameter time         ClkPeriod    = 10ns,
    parameter time         AcqDelay     = 9ns,
    parameter time         ApplDelay    = 1ns,
    parameter int unsigned MaxSimCycles = 1000
);
    // #######################################################################################
    // # Local Parameters                                                                    #
    // #######################################################################################

    localparam int unsigned WidWidth = NumWarps > 1 ? $clog2(NumWarps) : 1;
    localparam int unsigned TagWidth = $clog2(InflightInstrPerWarp);

    localparam int unsigned BlockAddrWidth = AddressWidth - BlockIdxBits;
    localparam int unsigned BlockWidth = 1 << BlockIdxBits;
    localparam int unsigned ThreadIdxWidth = WarpWidth > 1 ? $clog2(WarpWidth) : 1;

    localparam int unsigned ICAddrWidth = IClineIdxBits > 0 ? PcWidth - IClineIdxBits : PcWidth;

    // #######################################################################################
    // # Type Definitions                                                                    #
    // #######################################################################################

    typedef logic [7:0] byte_t;

    typedef logic  [          PcWidth-1:0] pc_t;
    typedef logic  [        WarpWidth-1:0] act_mask_t;
    typedef logic  [      RegIdxWidth-1:0] reg_idx_t;
    typedef logic  [WidWidth+TagWidth-1:0] iid_t;
    typedef logic  [   BlockAddrWidth-1:0] block_addr_t;
    typedef logic  [       BlockWidth-1:0] block_mask_t;
    typedef byte_t [       BlockWidth-1:0] block_data_t;
    typedef logic  [      ICAddrWidth-1:0] imem_addr_t;
    typedef logic  [     AddressWidth-1:0] addr_t;
    typedef logic  [    TblockIdxBits-1:0] tblock_idx_t;
    typedef logic  [     TgroupIdBits-1:0] tgroup_id_t;
    typedef logic  [OutstandingReqIdxWidth+ThreadIdxWidth-1:0] req_id_t;

    typedef struct packed {
        eu_e           eu;
        inst_subtype_t subtype;
        reg_idx_t      dst;
        reg_idx_t      op2;
        reg_idx_t      op1;
    } enc_inst_t;

    typedef enc_inst_t [(1 << IClineIdxBits)-1:0] imem_data_t;

    typedef struct packed {
        req_id_t     id;
        block_addr_t addr;
        block_mask_t we_mask;
        block_data_t data;
    } mem_req_t;

    typedef struct packed {
        req_id_t     id;
        block_data_t data;
    } mem_rsp_t;

    typedef struct packed {
        pc_t pc;
        addr_t dp_addr;
        tblock_idx_t tblock_idx;
        tgroup_id_t  tgroup_id;
    } warp_insert_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Flush instruction cache
    logic flush_ic;

    // Warp insertion
    logic         warp_free, allocate_warp;
    warp_insert_t warp_insert;

    // Warp completion
    logic       tblock_done;
    tgroup_id_t tblock_done_id;

    // Memory request
    logic     mem_ready, mem_req_valid;
    mem_req_t mem_req;

    // Memory response
    logic     mem_rsp_valid_q, mem_rsp_valid_d;
    mem_rsp_t mem_rsp_q,       mem_rsp_d;

    // Test program
    enc_inst_t test_program [13] = {
        // Calculate byte offset from thread ID and warp ID
        '{eu: EU_IU,  subtype: IU_TBID,        dst: 0, op1: 0, op2: 0}, // reg0 = warp ID

        // Load data from memory
        '{eu: EU_LSU, subtype: LSU_LOAD_BYTE,  dst: 1, op1: 0, op2: 0}, // reg1 = [reg0]

        // Subtract address from data
        '{eu: EU_IU,  subtype: IU_SUB,         dst: 2, op1: 1, op2: 1}, // reg2 = reg1 - reg0

        // '{eu: EU_IU,  subtype: IU_BID,         dst: 3, op1: 0, op2: 0}, // reg3 = block ID

        // '{eu: EU_IU,  subtype: IU_ADD,         dst: 4, op1: 2, op2: 3}, // reg4 = reg2 + reg3

        // Store result back to memory
        '{eu: EU_LSU, subtype: LSU_STORE_BYTE, dst: 5, op1: 2, op2: 0}, // [reg0] = reg4

        '{eu: EU_FPU, subtype: FPU_INT_TO_FP,  dst:  6, op1:  0, op2:  0},
        '{eu: EU_FPU, subtype: FPU_MUL,        dst:  7, op1:  6, op2:  6},
        '{eu: EU_FPU, subtype: FPU_FP_TO_INT,  dst:  8, op1:  7, op2:  7},
        '{eu: EU_FPU, subtype: FPU_DIV,        dst:  9, op1:  7, op2:  6},
        '{eu: EU_FPU, subtype: FPU_FP_TO_INT,  dst: 10, op1:  9, op2:  9},
        '{eu: EU_FPU, subtype: FPU_RECIP,      dst: 11, op1:  9, op2:  9},
        '{eu: EU_FPU, subtype: FPU_RECIP,      dst: 12, op1: 11, op2: 11},
        '{eu: EU_FPU, subtype: FPU_FP_TO_INT,  dst: 13, op1: 12, op2: 12},

        // NOPs
        '{eu: eu_e'('1),   subtype: '1,        dst: 0, op1: 0, op2: 0}  // STOP thread
    };
    // enc_inst_t test_program [14] = {
    //     // Calculate byte offset from thread ID and warp ID
    //     '{eu: EU_IU,  subtype: IU_TBID,        dst: 0, op1: 0, op2: 0}, // reg0 = thread ID in tblk
    //     '{eu: EU_BRU, subtype: BRU_SYNC,       dst: 0, op1: 0, op2: 0}, // Sync threads in warp

    //     // Load data from memory
    //     '{eu: EU_LSU, subtype: LSU_LOAD_BYTE,  dst: 1, op1: 0, op2: 0}, // reg1 = [reg0]

    //     // Subtract address from data
    //     '{eu: EU_IU,  subtype: IU_SUB,         dst: 2, op1: 1, op2: 0}, // reg2 = reg1 - reg0
    //     '{eu: EU_IU,  subtype: IU_LDI,         dst: 3, op1: 1, op2: 0}, // reg3 = 1
    //     '{eu: EU_IU,  subtype: IU_ADD,         dst: 2, op1: 2, op2: 3}, // reg2 = reg3 + reg2
    //     '{eu: EU_IU,  subtype: IU_AND,         dst: 3, op1: 3, op2: 0}, // reg3 = reg3 & reg2

    //     '{eu: EU_BRU, subtype: BRU_BEZ,        dst: 6, op1: 1, op2: 3}, // Jump if reg3 == 0
    //     // '{eu: EU_IU,  subtype: IU_SUB,         dst: 2, op1: 2, op2: 0}, // reg2 = reg2 - reg0
    //     '{eu: EU_IU,  subtype: IU_LDI,         dst: 2, op1: 255, op2: 0}, // reg2 = 255

    //     '{eu: EU_BRU, subtype: BRU_SYNC,       dst: 0, op1: 0, op2: 0}, // Sync threads in warp
    //     '{eu: EU_IU,  subtype: IU_BID,         dst: 3, op1: 0, op2: 0}, // reg3 = block ID

    //     '{eu: EU_IU,  subtype: IU_ADD,         dst: 4, op1: 2, op2: 3}, // reg4 = reg2 + reg3

    //     // Store result back to memory
    //     '{eu: EU_LSU, subtype: LSU_STORE_BYTE, dst: 5, op1: 0, op2: 2}, // [reg0] = reg4

    //     // NOPs
    //     '{eu: eu_e'('1),   subtype: '1,        dst: 0, op1: 0, op2: 0}  // STOP warps
    // };

    logic stop, clk, rst_n;

    // Instruction Cache requests
    logic       imem_ready, imem_req_valid;
    imem_addr_t imem_req_addr;

    // Instruction Cache response
    logic       imem_rsp_valid, imem_rsp_valid_q;
    imem_data_t imem_rsp_data, imem_rsp_data_q;

    imem_data_t imem_rsp_data_queue [$];

    // Memory
    block_data_t [SimMemBlocks-1:0] memory;

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
    // # DUT                                                                                 #
    // #######################################################################################

    // Instantiate Compute Unit
    compute_unit #(
    `ifndef TARGET_POST_SYNTH
        .WritebackWidth        ( WritebackWidth         ),
        .PcWidth               ( PcWidth                ),
        .NumWarps              ( NumWarps               ),
        .WarpWidth             ( WarpWidth              ),
        .EncInstWidth          ( $bits(enc_inst_t)      ),
        .InflightInstrPerWarp  ( InflightInstrPerWarp   ),
        .RegIdxWidth           ( RegIdxWidth            ),
        .OperandsPerInst       ( OperandsPerInst        ),
        .NumBanks              ( NumBanks               ),
        .NumOperandCollectors  ( NumOperandCollectors   ),
        .RegWidth              ( RegWidth               ),
        .AddressWidth          ( AddressWidth           ),
        .BlockIdxBits          ( BlockIdxBits           ),
        .OutstandingReqIdxWidth( OutstandingReqIdxWidth ),
        .NumIClines            ( NumIClines             ),
        .IClineIdxBits         ( IClineIdxBits          ),
        .TblockIdxBits         ( TblockIdxBits          ),
        .TgroupIdBits          ( TgroupIdBits           )
    `endif
    ) i_cu (
        .clk_i ( clk   ),
        .rst_ni( rst_n ),

        .inorder_execution_i( InorderExecution ),

        .testmode_i( 1'b0 ),

        .flush_ic_i( flush_ic ),

        .warp_free_o          ( warp_free              ),
        .allocate_warp_i      ( allocate_warp          ),
        .allocate_pc_i        ( warp_insert.pc         ),
        .allocate_dp_addr_i   ( warp_insert.dp_addr    ),
        .allocate_tblock_idx_i( warp_insert.tblock_idx ),
        .allocate_tgroup_id_i ( warp_insert.tgroup_id  ),

        .tblock_done_ready_i( 1'b1           ),
        .tblock_done_o      ( tblock_done    ),
        .tblock_done_id_o   ( tblock_done_id ),

        .imem_ready_i    ( imem_ready     ),
        .imem_req_valid_o( imem_req_valid ),
        .imem_req_addr_o ( imem_req_addr  ),

        .imem_rsp_valid_i( imem_rsp_valid_q ),
`ifdef TARGET_GOWIN_EDA_POSTSYNTH
        .imem_rsp_data_i_0( imem_rsp_data_q[0] ),
        .imem_rsp_data_i_1( imem_rsp_data_q[1] ),
        .imem_rsp_data_i_2( imem_rsp_data_q[2] ),
        .imem_rsp_data_i_3( imem_rsp_data_q[3] ),
`else
    `ifdef TARGET_XILINX_VIVADO_POSTSYNTH
        .imem_rsp_data_i_BRA_0_KET_( imem_rsp_data_q[0] ),
        .imem_rsp_data_i_BRA_1_KET_( imem_rsp_data_q[1] ),
        .imem_rsp_data_i_BRA_2_KET_( imem_rsp_data_q[2] ),
        .imem_rsp_data_i_BRA_3_KET_( imem_rsp_data_q[3] ),
    `else
        .imem_rsp_data_i( imem_rsp_data_q ),
    `endif
`endif

        .mem_ready_i      ( mem_ready       ),
        .mem_req_valid_o  ( mem_req_valid   ),
        .mem_req_id_o     ( mem_req.id      ),
        .mem_req_addr_o   ( mem_req.addr    ),
        .mem_req_we_mask_o( mem_req.we_mask ),
`ifdef TARGET_GOWIN_EDA_POSTSYNTH
        .mem_req_wdata_o_0 ( mem_req.data[ 0] ),
        .mem_req_wdata_o_1 ( mem_req.data[ 1] ),
        .mem_req_wdata_o_2 ( mem_req.data[ 2] ),
        .mem_req_wdata_o_3 ( mem_req.data[ 3] ),
        .mem_req_wdata_o_4 ( mem_req.data[ 4] ),
        .mem_req_wdata_o_5 ( mem_req.data[ 5] ),
        .mem_req_wdata_o_6 ( mem_req.data[ 6] ),
        .mem_req_wdata_o_7 ( mem_req.data[ 7] ),
        .mem_req_wdata_o_8 ( mem_req.data[ 8] ),
        .mem_req_wdata_o_9 ( mem_req.data[ 9] ),
        .mem_req_wdata_o_10( mem_req.data[10] ),
        .mem_req_wdata_o_11( mem_req.data[11] ),
        .mem_req_wdata_o_12( mem_req.data[12] ),
        .mem_req_wdata_o_13( mem_req.data[13] ),
        .mem_req_wdata_o_14( mem_req.data[14] ),
        .mem_req_wdata_o_15( mem_req.data[15] ),
`else
    `ifdef TARGET_XILINX_VIVADO_POSTSYNTH
        .mem_req_wdata_o_BRA_0_KET_ ( mem_req.data[ 0] ),
        .mem_req_wdata_o_BRA_1_KET_ ( mem_req.data[ 1] ),
        .mem_req_wdata_o_BRA_2_KET_ ( mem_req.data[ 2] ),
        .mem_req_wdata_o_BRA_3_KET_ ( mem_req.data[ 3] ),
        .mem_req_wdata_o_BRA_4_KET_ ( mem_req.data[ 4] ),
        .mem_req_wdata_o_BRA_5_KET_ ( mem_req.data[ 5] ),
        .mem_req_wdata_o_BRA_6_KET_ ( mem_req.data[ 6] ),
        .mem_req_wdata_o_BRA_7_KET_ ( mem_req.data[ 7] ),
        .mem_req_wdata_o_BRA_8_KET_ ( mem_req.data[ 8] ),
        .mem_req_wdata_o_BRA_9_KET_ ( mem_req.data[ 9] ),
        .mem_req_wdata_o_BRA_10_KET_( mem_req.data[10] ),
        .mem_req_wdata_o_BRA_11_KET_( mem_req.data[11] ),
        .mem_req_wdata_o_BRA_12_KET_( mem_req.data[12] ),
        .mem_req_wdata_o_BRA_13_KET_( mem_req.data[13] ),
        .mem_req_wdata_o_BRA_14_KET_( mem_req.data[14] ),
        .mem_req_wdata_o_BRA_15_KET_( mem_req.data[15] ),
    `else
        .mem_req_wdata_o( mem_req.data ),
    `endif
`endif

        .mem_rsp_valid_i( mem_rsp_valid_q ),
        .mem_rsp_id_i   ( mem_rsp_q.id    ),
`ifdef TARGET_GOWIN_EDA_POSTSYNTH
        .mem_rsp_data_i_0 ( mem_rsp_q.data[ 0] ),
        .mem_rsp_data_i_1 ( mem_rsp_q.data[ 1] ),
        .mem_rsp_data_i_2 ( mem_rsp_q.data[ 2] ),
        .mem_rsp_data_i_3 ( mem_rsp_q.data[ 3] ),
        .mem_rsp_data_i_4 ( mem_rsp_q.data[ 4] ),
        .mem_rsp_data_i_5 ( mem_rsp_q.data[ 5] ),
        .mem_rsp_data_i_6 ( mem_rsp_q.data[ 6] ),
        .mem_rsp_data_i_7 ( mem_rsp_q.data[ 7] ),
        .mem_rsp_data_i_8 ( mem_rsp_q.data[ 8] ),
        .mem_rsp_data_i_9 ( mem_rsp_q.data[ 9] ),
        .mem_rsp_data_i_10( mem_rsp_q.data[10] ),
        .mem_rsp_data_i_11( mem_rsp_q.data[11] ),
        .mem_rsp_data_i_12( mem_rsp_q.data[12] ),
        .mem_rsp_data_i_13( mem_rsp_q.data[13] ),
        .mem_rsp_data_i_14( mem_rsp_q.data[14] ),
        .mem_rsp_data_i_15( mem_rsp_q.data[15] )
`else
    `ifdef TARGET_XILINX_VIVADO_POSTSYNTH
        .mem_rsp_data_i_BRA_0_KET_ ( mem_rsp_q.data[ 0] ),
        .mem_rsp_data_i_BRA_1_KET_ ( mem_rsp_q.data[ 1] ),
        .mem_rsp_data_i_BRA_2_KET_ ( mem_rsp_q.data[ 2] ),
        .mem_rsp_data_i_BRA_3_KET_ ( mem_rsp_q.data[ 3] ),
        .mem_rsp_data_i_BRA_4_KET_ ( mem_rsp_q.data[ 4] ),
        .mem_rsp_data_i_BRA_5_KET_ ( mem_rsp_q.data[ 5] ),
        .mem_rsp_data_i_BRA_6_KET_ ( mem_rsp_q.data[ 6] ),
        .mem_rsp_data_i_BRA_7_KET_ ( mem_rsp_q.data[ 7] ),
        .mem_rsp_data_i_BRA_8_KET_ ( mem_rsp_q.data[ 8] ),
        .mem_rsp_data_i_BRA_9_KET_ ( mem_rsp_q.data[ 9] ),
        .mem_rsp_data_i_BRA_10_KET_( mem_rsp_q.data[10] ),
        .mem_rsp_data_i_BRA_11_KET_( mem_rsp_q.data[11] ),
        .mem_rsp_data_i_BRA_12_KET_( mem_rsp_q.data[12] ),
        .mem_rsp_data_i_BRA_13_KET_( mem_rsp_q.data[13] ),
        .mem_rsp_data_i_BRA_14_KET_( mem_rsp_q.data[14] ),
        .mem_rsp_data_i_BRA_15_KET_( mem_rsp_q.data[15] )
    `else
        .mem_rsp_data_i( mem_rsp_q.data )
    `endif
`endif
    );

    // #######################################################################################
    // # Launching Threadblocks                                                              #
    // #######################################################################################

    initial begin : launch_tblocks
        int unsigned tblocks_launched;
        tblocks_launched = 0;

        repeat (5) @(posedge clk);
        wait(rst_n);

        while (tblocks_launched < TblocksToLaunch) begin
            @(posedge clk);
            #ApplDelay;
            // Flush IC if it is the first threadblock
            flush_ic = (tblocks_launched == 0);

            allocate_warp          = 1'b1;
            warp_insert.pc         = '0;
            warp_insert.dp_addr    =       addr_t'(tblocks_launched);
            warp_insert.tblock_idx = tblock_idx_t'(tblocks_launched);
            warp_insert.tgroup_id  =  tgroup_id_t'(tblocks_launched);

            if (warp_free) begin
                tblocks_launched++;
            end
        end

        @(posedge clk);
        #ApplDelay;
        allocate_warp = 1'b0;

        $display("Launched %0d thread blocks.", tblocks_launched);

    end : launch_tblocks

    initial begin : wait_tblocks_done
        // Wait for all thread blocks to finish
        int unsigned tblocks_done;
        tblocks_done = 0;

        while (tblocks_done < TblocksToLaunch) begin
            @(posedge clk);
            #AcqDelay;
            if (tblock_done) begin
                $display("Thread block %0d done.", tblock_done_id);
                tblocks_done++;
                tblock_done = 1'b0;
            end
        end

        $display("All thread blocks done.");
        stop = 1'b1;

    end : wait_tblocks_done

    // #######################################################################################
    // # Memory                                                                              #
    // #######################################################################################

    // Instruction memory request
    initial begin
        imem_data_t rsp;
        imem_ready = 1'b1;

        while (1) begin
            @(posedge clk);
            #AcqDelay;
            if (imem_req_valid && imem_ready) begin
                rsp = '0;
                for (int i = 0; i < (1 << IClineIdxBits); i++) begin
                    if (i + imem_req_addr * (1 << IClineIdxBits) < $size(test_program)) begin
                        // Fetch instruction from test program
                        rsp[i] = test_program[i + imem_req_addr * (1 << IClineIdxBits)];
                    end
                end
                $display("Instruction Cache request: Addr %0d Data %h",
                    imem_req_addr, rsp);
                imem_rsp_data_queue.push_back(rsp);
            end
        end
    end

    initial begin
        while (1) begin
            @(posedge clk);
            #ApplDelay;
            imem_rsp_valid = 1'b0;
            if (imem_rsp_data_queue.size() > 0) begin
                // Pop the first instruction from the queue
                imem_rsp_data = imem_rsp_data_queue.pop_front();
                imem_rsp_valid = 1'b1;
                $display("Instruction Cache response: Addr %0d Data %h",
                    imem_req_addr, imem_rsp_data);
            end
        end
    end

    always_ff @(posedge clk) begin
        // Instruction Cache response
        imem_rsp_valid_q <= imem_rsp_valid;
        imem_rsp_data_q  <= imem_rsp_data;
    end

    // Memory read/write
    initial begin
        int val;

        mem_ready = 1'b0;
        for (int i = 0; i < SimMemBlocks; i++) begin
            for (int j = 0; j < BlockWidth; j++) begin
                val = i * BlockWidth + j;
                memory[i][j] = val[7:0];
            end
        end

        mem_ready = 1'b1;

        while (1) begin
            @(posedge clk);
            #AcqDelay;
            mem_rsp_valid_d = 1'b0;

            if (mem_req_valid) begin
                assert(int'(mem_req.addr) < SimMemBlocks)
                else $error("Memory write request out of bounds: Addr %0d", mem_req.addr);

                if (mem_req.we_mask != '0) begin
                    // Write request
                    $display("Memory write request: ID %0d Addr %0d WeMask %b Data %h",
                        mem_req.id, mem_req.addr, mem_req.we_mask, mem_req.data);
                    for (int i = 0; i < BlockWidth; i++) begin
                        if (mem_req.we_mask[i]) begin
                            memory[mem_req.addr][i] = mem_req.data[i];
                        end
                    end
                    mem_rsp_d.data = '0;
                end else begin
                    // Read request
                    $display("Memory read request: ID %0d Addr %0d", mem_req.id, mem_req.addr);
                    mem_rsp_d.data  = memory[mem_req.addr];
                end
                mem_rsp_valid_d = 1'b1;
                mem_rsp_d.id    = mem_req.id;
            end
        end
    end

    always_ff @(posedge clk) begin
        // Memory response
        mem_rsp_valid_q <= mem_rsp_valid_d;
        mem_rsp_q       <= mem_rsp_d;
    end

    // ########################################################################################
    // # Simulation Logic                                                                     #
    // ########################################################################################

    // Monitor output
    int cycles;
    initial begin
        cycles = 0;

        $timeformat(-9, 0, "ns", 12);
        // configure VCD dump
        $dumpfile("cu.vcd");
        $dumpvars();

        while (1) begin
            @(posedge clk);
            #AcqDelay;
            $display("Cycle %4d Time %8d", cycles, $time);
            if (rst_n) begin
                // Output from fetcher
                `ifndef POST
                $display("Fetcher output valid: %b", i_cu.fe_to_ic_valid_d);
                if (i_cu.fe_to_ic_valid_d) begin
                    $display("Instruction at PC %d", i_cu.fe_to_ic_data_d.pc);
                    $display("Act. mask:        %b", i_cu.fe_to_ic_data_d.act_mask);
                    $display("Warp ID:          %d", i_cu.fe_to_ic_data_d.warp_id);
                end else begin
                    $display("Instruction at PC X");
                    $display("Act. mask:        X");
                    $display("Warp ID:          X");
                end

                $display("Decoder output valid: %b", i_cu.dec_to_ib_valid_q);
                if (i_cu.dec_to_ib_valid_q) begin
                    $display("Instruction at PC %d", i_cu.dec_to_ib_data_q.pc);
                    $display("Act. mask:        %b", i_cu.dec_to_ib_data_q.act_mask);
                    $display("Warp ID:          %d", i_cu.dec_to_ib_data_q.warp_id);
                end else begin
                    $display("Instruction at PC X");
                    $display("Act. mask:        X");
                    $display("Warp ID:          X");
                end
                `endif
            end

            cycles++;

            $display("\n");
        end
    end
    `ifndef POST
    for (genvar warp = 0; warp < NumWarps; warp++) begin : gen_display_dispatcher
        initial begin
            while (1) begin
                @(posedge clk);
                #AcqDelay;
                $display("Warp %2d", warp);
                $display("Register Table");
                $display("Entry   Vld Dst Prod Subwarp");
                for (int rtentry = 0; rtentry < InflightInstrPerWarp; rtentry++) begin : gen_disp_rt
                    $display("RT[%2d]: %1d  %2d  %2d  %2d",
                        rtentry,
                        i_cu.i_warp_dispatcher.gen_dispatcher[warp]
                            .i_dispatcher.i_reg_table.table_valid_q[rtentry],
                        i_cu.i_warp_dispatcher.gen_dispatcher[warp]
                            .i_dispatcher.i_reg_table.table_q[rtentry].dst,
                        i_cu.i_warp_dispatcher.gen_dispatcher[warp]
                            .i_dispatcher.i_reg_table.table_q[rtentry].producer,
                        i_cu.i_warp_dispatcher.gen_dispatcher[warp]
                            .i_dispatcher.i_reg_table.table_q[rtentry].subwarp_id
                    );
                end : gen_disp_rt
                $display();

                $display("Wait buffer");
                $write("Entry   Vld Rdy PC  Tag Dst");
                for (int operand = 0; operand < OperandsPerInst; operand++) begin
                    $write("  Rdy Tag Op%1d", operand);
                end
                $write(" Disp Dpmask");
                $display();
                for (int wbentry = 0; wbentry < InflightInstrPerWarp; wbentry++) begin
                    $write("WB[%2d]: %1d   %1d %4d  %2d %2d",
                        wbentry,
                        i_cu.i_warp_dispatcher.gen_dispatcher[warp]
                            .i_dispatcher.i_wait_buffer.wait_buffer_valid_q[wbentry],
                        i_cu.i_warp_dispatcher.gen_dispatcher[warp]
                            .i_dispatcher.i_wait_buffer.rr_inst_ready[wbentry],
                        i_cu.i_warp_dispatcher.gen_dispatcher[warp]
                            .i_dispatcher.i_wait_buffer.wait_buffer_q[wbentry].pc,
                        i_cu.i_warp_dispatcher.gen_dispatcher[warp]
                            .i_dispatcher.i_wait_buffer.wait_buffer_q[wbentry].tag,
                        i_cu.i_warp_dispatcher.gen_dispatcher[warp]
                            .i_dispatcher.i_wait_buffer.wait_buffer_q[wbentry].dst_reg
                    );
                    for (int operand = 0; operand < OperandsPerInst; operand++) begin
                        $write("    %1d  %2d  %2d",
                            i_cu.i_warp_dispatcher.gen_dispatcher[warp]
                                .i_dispatcher.i_wait_buffer.wait_buffer_q[wbentry]
                                    .operands_ready[operand],
                            i_cu.i_warp_dispatcher.gen_dispatcher[warp]
                                .i_dispatcher.i_wait_buffer.wait_buffer_q[wbentry]
                                    .operand_tags[operand],
                            i_cu.i_warp_dispatcher.gen_dispatcher[warp]
                                .i_dispatcher.i_wait_buffer.wait_buffer_q[wbentry]
                                    .operands[operand]);
                    end
                    $write("   %1d    %b",
                        i_cu.i_warp_dispatcher.gen_dispatcher[warp]
                            .i_dispatcher.i_wait_buffer.wait_buffer_dispatched_q[wbentry],
                        i_cu.i_warp_dispatcher.gen_dispatcher[warp]
                            .i_dispatcher.i_wait_buffer.wait_buffer_q[wbentry].dep_mask);
                    $display();
                end
                $display();
            end
        end
    end : gen_display_dispatcher

    initial begin : kanata_format
        int fd;
        logic [(PcWidth + WarpWidth + WidWidth)-1:0] insn_id_in_sim;

        // Hashmap for sim id to file id
        int insn_id_in_file;
        int insn_id_in_file_counter;
        int insn_id_in_file_map[logic[(PcWidth + WarpWidth + WidWidth)-1:0]];

        // OPC tag to file id
        int opc_insn_id_in_file[iid_t];
        int retire_id;
        retire_id = 0;

        insn_id_in_file_counter = 0;

        fd = $fopen("pipeline.out", "w");

        // Header
        $fwrite(fd, "Kanata\t0004\n");
        // Start time
        $fwrite(fd, "C=\t0\n");

        while (!stop) begin
            @(posedge clk);
            #AcqDelay;
            // Cycle
            $fwrite(fd, "C\t1\n");

            // Fetcher
            if (i_cu.fe_to_ic_valid_d && i_cu.ic_to_fe_ready_q) begin
                insn_id_in_sim[PcWidth-1:0] = i_cu.fe_to_ic_data_d.pc;
                insn_id_in_sim[PcWidth + WarpWidth - 1:PcWidth] = i_cu.fe_to_ic_data_d.act_mask;
                insn_id_in_sim[PcWidth + WarpWidth + WidWidth - 1:PcWidth + WarpWidth] =
                    i_cu.fe_to_ic_data_d.warp_id;

                // Add to hashmap
                assert(insn_id_in_file_map[insn_id_in_sim] == 0)
                else $warning("Instruction %0d already exists in file.", insn_id_in_sim);

                insn_id_in_file_map[insn_id_in_sim] = insn_id_in_file_counter;
                insn_id_in_file = insn_id_in_file_counter;
                insn_id_in_file_counter++;

                // New instruction
                $fwrite(fd, "I\t%0d\t%0d\t%0d\n",
                    insn_id_in_file,
                    insn_id_in_sim,
                    i_cu.fe_to_ic_data_d.warp_id);

                // Instruction Info
                $fwrite(fd, "L\t%0d\t0\tWarp %0d PC: %0d\n",
                    insn_id_in_file,
                    i_cu.fe_to_ic_data_d.warp_id,
                    i_cu.fe_to_ic_data_d.pc);

                // Fetch Stage
                $fwrite(fd, "S\t%0d\t0\tF\n",
                    insn_id_in_file);
            end

            // Instruction Cache
            if (i_cu.fe_to_ic_valid_q && i_cu.ic_to_fe_ready_d) begin
                // Get the instruction ID from the hashmap
                insn_id_in_sim[PcWidth-1:0] = i_cu.fe_to_ic_data_q.pc;
                insn_id_in_sim[PcWidth + WarpWidth - 1:PcWidth] = i_cu.fe_to_ic_data_q.act_mask;
                insn_id_in_sim[PcWidth + WarpWidth + WidWidth - 1:PcWidth + WarpWidth] =
                    i_cu.fe_to_ic_data_q.warp_id;
                insn_id_in_file = insn_id_in_file_map[insn_id_in_sim];

                // Instruction Cache Stage
                $fwrite(fd, "S\t%0d\t0\tIC\n",
                    insn_id_in_file);
            end

            // Decoder
            // TODO: Multiple instructions
            if ((|i_cu.ic_to_dec_valid) && i_cu.dec_to_ic_ready) begin
                // Get the instruction ID from the hashmap
                insn_id_in_sim[PcWidth-1:0] = i_cu.ic_to_dec_data.pc;
                insn_id_in_sim[PcWidth + WarpWidth - 1:PcWidth] = i_cu.ic_to_dec_data.act_mask;
                insn_id_in_sim[PcWidth + WarpWidth + WidWidth - 1:PcWidth + WarpWidth] =
                    i_cu.ic_to_dec_data.warp_id;
                insn_id_in_file = insn_id_in_file_map[insn_id_in_sim];

                // Decoder Stage
                $fwrite(fd, "S\t%0d\t0\tD\n",
                    insn_id_in_file);

                // Control Instruction -> Retire this instruction
                if (i_cu.dec_to_fetch_control) begin
                    // Retire
                    $fwrite(fd, "R\t%0d\t%0d\t0\n",
                        insn_id_in_file, retire_id);
                    retire_id++;
                end
            end

            // Start Dispatcher Stage
            if (i_cu.dec_to_ib_valid_q && i_cu.ib_to_dec_ready_d) begin
                // Get the instruction ID from the hashmap
                insn_id_in_sim[PcWidth-1:0] = i_cu.dec_to_ib_data_q.pc;
                insn_id_in_sim[PcWidth + WarpWidth - 1:PcWidth] = i_cu.dec_to_ib_data_q.act_mask;
                insn_id_in_sim[PcWidth + WarpWidth + WidWidth - 1:PcWidth + WarpWidth] =
                    i_cu.dec_to_ib_data_q.warp_id;
                insn_id_in_file = insn_id_in_file_map[insn_id_in_sim];

                // Dispatcher Stage
                $fwrite(fd, "S\t%0d\t0\tIB\n",
                    insn_id_in_file);
            end

            // Start OPC Stage
            if (i_cu.disp_to_opc_valid && i_cu.opc_to_disp_ready) begin
                // Get the instruction ID from the hashmap
                insn_id_in_sim[PcWidth-1:0] = i_cu.disp_to_opc_data.pc;
                insn_id_in_sim[PcWidth + WarpWidth - 1:PcWidth] = i_cu.disp_to_opc_data.act_mask;
                insn_id_in_sim[PcWidth + WarpWidth + WidWidth - 1:PcWidth + WarpWidth] =
                    i_cu.disp_to_opc_data.tag[WidWidth-1:0];
                insn_id_in_file = insn_id_in_file_map[insn_id_in_sim];

                opc_insn_id_in_file[i_cu.disp_to_opc_data.tag] = insn_id_in_file;

                // OPC Stage
                $fwrite(fd, "S\t%0d\t0\tOpC\n",
                    insn_id_in_file);
            end

            // Execute Stage
            if (i_cu.opc_to_eu_valid_q && i_cu.eu_to_opc_ready_d) begin
                // Get the instruction ID from the hashmap
                insn_id_in_file = opc_insn_id_in_file[i_cu.opc_to_eu_data_q.tag];

                // Execute Stage
                $fwrite(fd, "S\t%0d\t0\tEu\n",
                    insn_id_in_file);
            end

            // Retire
            for (int wb = 0; wb < WritebackWidth; wb++) begin : loop_writeback_ports
                if (i_cu.eu_to_opc_valid_q[wb] && i_cu.opc_to_eu_ready_d[wb]) begin
                    insn_id_in_file = opc_insn_id_in_file[i_cu.eu_to_opc_data_q[wb].tag];

                    // Retire
                    $fwrite(fd, "R\t%0d\t%0d\t0\n",
                        insn_id_in_file, retire_id);
                    retire_id++;
                end
            end : loop_writeback_ports
        end

        // Close file
        $fclose(fd);
    end : kanata_format
    `endif

    // Max simulation cycles
    logic error;
    initial begin
        error = 1'b0;
        repeat(MaxSimCycles) @(posedge clk);
        $display("Max simulation cycles reached.");
        stop  = 1'b1;
        error = 1'b1;
    end

    // Stop simulation
    initial begin
        wait(stop);
        $display("Stopping simulation...");
        $dumpflush;

        for (int i = 0; i < SimMemBlocks; i++) begin
            $display("Memory block[%0d]: %h", i, memory[i]);
        end

        if (error)
            $fatal(1);
        else
            $finish;
    end

    initial assert(TblocksToLaunch <= (1 << TblockIdxBits))
    else $error("TblocksToLaunch (%0d) exceeds maximum number of thread blocks (%0d).",
        TblocksToLaunch, (1 << TblockIdxBits));

endmodule : tb_compute_unit
