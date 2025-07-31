// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Testbench for Compute Cluster
module tb_compute_cluster import bgpu_pkg::*; #(
    /// Number of Compute Units in the cluster
    parameter int unsigned ComputeUnits = 4,
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
    // Memory Block index width -> Memory request width is 2^BlockIdxBits bytes
    parameter int unsigned BlockIdxBits = 4,
    /// Width of a memory address
    parameter int unsigned AddressWidth = 24,
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

    parameter int unsigned TblocksToLaunch = 255,
    parameter int unsigned SimMemBlocks    = 65,
    parameter time         ClkPeriod       = 10ns,
    parameter time         ApplDelay       = 1ns,
    parameter time         AcqDelay        = 9ns,
    parameter int unsigned MaxSimCycles    = 1000
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

    // Unique ID for each compute unit
    localparam int unsigned ImemAxiIdWidth = ComputeUnits > 1 ? $clog2(ComputeUnits) + 1 : 1;
    // Unique ID for each compute unit + Outstanding request idx width
    localparam int unsigned MemAxiIdWidth = $clog2(ComputeUnits) + OutstandingReqIdxWidth
                                            + ThreadIdxWidth;

    // #######################################################################################
    // # Type Definitions                                                                    #
    // #######################################################################################

    typedef logic [          PcWidth-1:0] pc_t;
    typedef logic [        WarpWidth-1:0] act_mask_t;
    typedef logic [      RegIdxWidth-1:0] reg_idx_t;
    typedef logic [WidWidth+TagWidth-1:0] iid_t;
    typedef logic [   BlockAddrWidth-1:0] block_addr_t;
    typedef logic [       BlockWidth-1:0] block_mask_t;
    typedef logic [  BlockWidth * 8 -1:0] block_data_t;
    typedef logic [      ICAddrWidth-1:0] imem_addr_t;
    typedef logic [     AddressWidth-1:0] addr_t;
    typedef logic [    TblockIdxBits-1:0] tblock_idx_t;
    typedef logic [     TgroupIdBits-1:0] tgroup_id_t;
    typedef logic [OutstandingReqIdxWidth+ThreadIdxWidth-1:0] req_id_t;

    typedef struct packed {
        eu_e           eu;
        inst_subtype_t subtype;
        reg_idx_t      dst;
        reg_idx_t      op2;
        reg_idx_t      op1;
    } enc_inst_t;

    typedef logic [$bits(enc_inst_t) * (1 << IClineIdxBits) / 8-1:0] imem_data_strb_t;
    typedef logic [$bits(enc_inst_t) * (1 << IClineIdxBits)    -1:0] imem_data_t;

    typedef struct packed {
        pc_t pc;
        addr_t dp_addr;
        tblock_idx_t tblock_idx;
        tgroup_id_t  tgroup_id;
    } warp_insert_t;

    typedef logic [ImemAxiIdWidth-1:0] imem_axi_id_t;
    typedef logic [MemAxiIdWidth -1:0] mem_axi_id_t;

    localparam int unsigned ImemAxiAddrWidth = PcWidth + $clog2($bits(enc_inst_t) / 8);
    typedef logic [ImemAxiAddrWidth-1:0] imem_axi_addr_t;

    `AXI_TYPEDEF_ALL(imem_axi, imem_axi_addr_t, imem_axi_id_t, imem_data_t, imem_data_strb_t,
        logic)


    `AXI_TYPEDEF_ALL(mem_axi, addr_t, mem_axi_id_t, block_data_t, block_mask_t, logic)

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Warp insertion
    logic         warp_free, allocate_warp;
    warp_insert_t warp_insert;

    // Warp completion
    logic       tblock_done;
    tgroup_id_t tblock_done_id;

    // Test program
    enc_inst_t test_program [5] = {
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

        // NOPs
        '{eu: eu_e'('1),   subtype: '1,        dst: 0, op1: 0, op2: 0}  // STOP thread
    };

    logic stop, clk, rst_n;

    // Instruction Memory AXI interface
    imem_axi_req_t  imem_axi_req;
    imem_axi_resp_t imem_axi_rsp;

    // Memory AXI interface
    mem_axi_req_t  mem_axi_req;
    mem_axi_resp_t mem_axi_rsp;

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

    // Instantiate Compute Cluster
    compute_cluster #(
    `ifndef POST
        .ComputeUnits          ( ComputeUnits           ),
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
        .TgroupIdBits          ( TgroupIdBits           ),

        .imem_axi_req_t ( imem_axi_req_t  ),
        .imem_axi_resp_t( imem_axi_resp_t ),

        .mem_axi_req_t ( mem_axi_req_t  ),
        .mem_axi_resp_t( mem_axi_resp_t )
    `endif
    ) i_cc (
        .clk_i ( clk   ),
        .rst_ni( rst_n ),

        .testmode_i( 1'b0 ),

        .warp_free_o          ( warp_free              ),
        .allocate_warp_i      ( allocate_warp          ),
        .allocate_pc_i        ( warp_insert.pc         ),
        .allocate_dp_addr_i   ( warp_insert.dp_addr    ),
        .allocate_tblock_idx_i( warp_insert.tblock_idx ),
        .allocate_tgroup_id_i ( warp_insert.tgroup_id  ),

        .tblock_done_ready_i( 1'b1           ),
        .tblock_done_o      ( tblock_done    ),
        .tblock_done_id_o   ( tblock_done_id ),

        .imem_req_o( imem_axi_req ),
        .imem_rsp_i( imem_axi_rsp ),

        .mem_req_o ( mem_axi_req ),
        .mem_rsp_i ( mem_axi_rsp )
    );

    // #######################################################################################
    // # Launching Threadblocks                                                              #
    // #######################################################################################

    initial begin : launch_tblocks
        int unsigned tblocks_launched;
        tblocks_launched = 0;

        repeat (5) @(posedge clk);
        wait(rst_n);

        while(tblocks_launched < TblocksToLaunch) begin
            @(posedge clk);
            #ApplDelay;
            allocate_warp          = 1'b1;
            warp_insert.pc         = '0;
            warp_insert.dp_addr    =       addr_t'(tblocks_launched);
            warp_insert.tblock_idx = tblock_idx_t'(tblocks_launched);
            warp_insert.tgroup_id  =  tgroup_id_t'(tblocks_launched);

            if (warp_free) begin
                $display("Launching thread block %0d at address %0h.", tblocks_launched,
                    warp_insert.dp_addr);
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

        while(tblocks_done < TblocksToLaunch) begin
            @(posedge clk);
            #AcqDelay;
            if (tblock_done) begin
                tblocks_done++;
                $display("Thread block %d done. Completed %d blocks", tblock_done_id, tblocks_done);
            end
        end

        $display("All thread blocks done.");
        stop = 1'b1;

    end : wait_tblocks_done

    // #######################################################################################
    // # Memory                                                                              #
    // #######################################################################################

    // Initialize instruction memory
    initial begin : init_imem
        enc_inst_t inst;
        $display("Initializing instruction memory with %0d instructions.", $size(test_program));
        for (int unsigned i = 0; i < $size(test_program); i++) begin
            inst = test_program[i];
            for (int unsigned b = 0; b < $bits(enc_inst_t) / 8; b++) begin
                i_imem.mem[imem_axi_addr_t'((i * $bits(enc_inst_t) / 8) + b)] = inst[b * 8 +: 8];
            end
        end
    end : init_imem

    // Instruction Memory
    axi_sim_mem #(
        .AddrWidth        ( ImemAxiAddrWidth   ),
        .DataWidth        ( $bits(imem_data_t) ),
        .IdWidth          ( ImemAxiIdWidth     ),
        .UserWidth        ( 1                  ),
        .NumPorts         ( 1                  ),
        .axi_req_t        ( imem_axi_req_t     ),
        .axi_rsp_t        ( imem_axi_resp_t    ),
        .WarnUninitialized( 1'b1               ),
        .UninitializedData( "ones"             ), // Stops threads if they fetch uninitialized data
        .ClearErrOnAccess ( 1'b0               ),
        .ApplDelay        ( ApplDelay          ),
        .AcqDelay         ( AcqDelay           )
    ) i_imem (
        .clk_i ( clk   ),
        .rst_ni( rst_n ),

        .axi_req_i( imem_axi_req ),
        .axi_rsp_o( imem_axi_rsp ),

        .mon_w_valid_o     ( /* Unused */ ),
        .mon_w_addr_o      ( /* Unused */ ),
        .mon_w_data_o      ( /* Unused */ ),
        .mon_w_id_o        ( /* Unused */ ),
        .mon_w_user_o      ( /* Unused */ ),
        .mon_w_beat_count_o( /* Unused */ ),
        .mon_w_last_o      ( /* Unused */ ),

        .mon_r_valid_o     ( /* Unused */ ),
        .mon_r_addr_o      ( /* Unused */ ),
        .mon_r_data_o      ( /* Unused */ ),
        .mon_r_id_o        ( /* Unused */ ),
        .mon_r_user_o      ( /* Unused */ ),
        .mon_r_beat_count_o( /* Unused */ ),
        .mon_r_last_o      ( /* Unused */ )
    );

    // Instruction Memory Monitor
    axi_dumper #(
        .BusName   ( "imem"          ),
        .LogAW     ( 1'b1            ),
        .LogAR     ( 1'b1            ),
        .LogW      ( 1'b1            ),
        .LogB      ( 1'b1            ),
        .LogR      ( 1'b1            ),
        .axi_req_t ( imem_axi_req_t  ),
        .axi_resp_t( imem_axi_resp_t )
    ) i_imem_monitor (
        .clk_i ( clk   ),
        .rst_ni( rst_n ),

        .axi_req_i ( imem_axi_req ),
        .axi_resp_i( imem_axi_rsp )
    );

    // Initialize data memory
    initial begin : init_mem
        for (int unsigned i = 0; i < SimMemBlocks * BlockWidth; i++) begin
            i_mem.mem[addr_t'(i)] = i[7:0];
        end
    end : init_mem

    // Data Memory
    axi_sim_mem #(
        .AddrWidth        ( AddressWidth        ),
        .DataWidth        ( BlockWidth * 8      ),
        .IdWidth          ( MemAxiIdWidth       ),
        .UserWidth        ( 1                   ),
        .NumPorts         ( 1                   ),
        .axi_req_t        ( mem_axi_req_t       ),
        .axi_rsp_t        ( mem_axi_resp_t      ),
        .WarnUninitialized( 1'b1                ),
        .UninitializedData( "ones"              ),
        .ClearErrOnAccess ( 1'b0                ),
        .ApplDelay        ( ApplDelay           ),
        .AcqDelay         ( AcqDelay            )
    ) i_mem (
        .clk_i ( clk   ),
        .rst_ni( rst_n ),

        .axi_req_i( mem_axi_req ),
        .axi_rsp_o( mem_axi_rsp ),

        .mon_w_valid_o     ( /* Unused */ ),
        .mon_w_addr_o      ( /* Unused */ ),
        .mon_w_data_o      ( /* Unused */ ),
        .mon_w_id_o        ( /* Unused */ ),
        .mon_w_user_o      ( /* Unused */ ),
        .mon_w_beat_count_o( /* Unused */ ),
        .mon_w_last_o      ( /* Unused */ ),

        .mon_r_valid_o     ( /* Unused */ ),
        .mon_r_addr_o      ( /* Unused */ ),
        .mon_r_data_o      ( /* Unused */ ),
        .mon_r_id_o        ( /* Unused */ ),
        .mon_r_user_o      ( /* Unused */ ),
        .mon_r_beat_count_o( /* Unused */ ),
        .mon_r_last_o      ( /* Unused */ )
    );

    // Memory Monitor
    axi_dumper #(
        .BusName   ( "mem"          ),
        .LogAW     ( 1'b1           ),
        .LogAR     ( 1'b1           ),
        .LogW      ( 1'b1           ),
        .LogB      ( 1'b1           ),
        .LogR      ( 1'b1           ),
        .axi_req_t ( mem_axi_req_t  ),
        .axi_resp_t( mem_axi_resp_t )
    ) i_mem_monitor (
        .clk_i ( clk   ),
        .rst_ni( rst_n ),

        .axi_req_i ( mem_axi_req ),
        .axi_resp_i( mem_axi_rsp )
    );

    // ########################################################################################
    // # Simulation Logic                                                                     #
    // ########################################################################################

    // Monitor output
    int cycles;
    initial begin
        cycles = 0;
        stop   = 1'b0;
        error  = 1'b0;

        $timeformat(-9, 0, "ns", 12);
        // configure VCD dump
        $dumpfile("cc.vcd");
        $dumpvars(1,i_cu);

        while(1) begin
            @(posedge clk);
            #AcqDelay;
            $display("Cycle %4d Time %8d", cycles, $time);
            cycles++;
        end
    end

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
        block_data_t block_data;

        wait(stop);

        $display("Stopping simulation...");
        $dumpflush;

        for (int block = 0; block < SimMemBlocks; block++) begin
            for (int b = 0; b < BlockWidth; b++) begin
                block_data[b * 8 +: 8] = i_mem.mem[addr_t'(block * BlockWidth + b)];
            end
            $display("Memory block[%0d]: %h", block, block_data);
        end

        if (error)
            $fatal(1);
        else
            $finish;
    end

    initial assert(TblocksToLaunch <= (1 << TblockIdxBits))
    else $error("TblocksToLaunch (%0d) exceeds maximum number of thread blocks (%0d).",
        TblocksToLaunch, (1 << TblockIdxBits));

endmodule : tb_compute_cluster
