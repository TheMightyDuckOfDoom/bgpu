// Copyright 2025-2026 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`ifndef BENCHMARK
    `define BENCHMARK "add_2"
`endif

/// BGPU SoC top-level module testbench
module tb_bgpu_soc #(
    parameter time ClkPeriodMgmt = 25ns,
    parameter time ClkPeriodJtag = 50ns,
    parameter time ClkPeriod     = 10ns,

    parameter time ApplyDelay = 1ns,
    parameter time AcqDelay   = 0.9ns,

    parameter int unsigned MaxCycles = 10000000,

    parameter bit    InorderExecution = 1'b0,
    parameter string Benchmark        = `BENCHMARK
) ();
    // #######################################################################################
    // # Local Parameters                                                                    #
    // #######################################################################################

    // #######################################################################################
    // # Type Definitions                                                                    #
    // #######################################################################################

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Clock and Reset
    logic clk, rst_n;

    // Management Clock
    logic mgmt_clk;

    // JTAG Interface
    logic jtag_tck, jtag_tdi, jtag_tdo, jtag_tms, jtag_trst_n;

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

    clk_rst_gen #(
        .ClkPeriod   ( ClkPeriodMgmt ),
        .RstClkCycles( 3             )
    ) i_clk_mgmt_rst_gen (
        .clk_o ( mgmt_clk ),
        .rst_no()
    );

    clk_rst_gen #(
        .ClkPeriod   ( ClkPeriodJtag ),
        .RstClkCycles( 3             )
    ) i_clk_jtag_rst_gen (
        .clk_o ( jtag_tck     ),
        .rst_no( /* Unused */ )
    );

    // #######################################################################################
    // # DUT                                                                                 #
    // #######################################################################################

    bgpu_soc i_bgpu_soc (
        .clk_i ( clk   ),
        .rst_ni( rst_n ),

        .testmode_i( 1'b0 ),

        .mgmt_cpu_clk_i( mgmt_clk ),

        .jtag_tck_i  ( jtag_tck    ),
        .jtag_tdi_i  ( jtag_tdi    ),
        .jtag_tdo_o  ( jtag_tdo    ),
        .jtag_tms_i  ( jtag_tms    ),
        .jtag_trst_ni( jtag_trst_n ),

        .mctrl_axi_req_o( /* Not Connected */ ),
        .mctrl_axi_rsp_i( '0                  )
    );

    // #######################################################################################
    // # JTAG Debug Interface                                                                #
    // #######################################################################################

    localparam dm::sbcs_t JtagInitSbcs = dm::sbcs_t'{
        sbautoincrement: 1'b1, sbreadondata: 1'b1, sbaccess: 3, default: '0};

    riscv_dbg_simple_bgpu #(
        .IrLength ( 5 ),
        .TA       ( ClkPeriodJtag * 0.1 ),
        .TT       ( ClkPeriodJtag * 0.9 )
    ) jtag_dbg (
        .jtag_tck_i  ( jtag_tck    ),
        .jtag_trst_no( jtag_trst_n ),
        .jtag_tms_o  ( jtag_tms    ),
        .jtag_tdi_o  ( jtag_tdi    ),
        .jtag_tdo_i  ( jtag_tdo    )
    );

    initial begin : reset_jtag
        #(ClkPeriodJtag/2);
        jtag_dbg.reset_master();
    end : reset_jtag

    task automatic jtag_init;
        logic [31:0] idcode;
        dm::dmcontrol_t dmcontrol = '{dmactive: 1, default: '0};
        // Check ID code
        repeat(100) @(posedge jtag_tck);
        jtag_dbg.get_idcode(idcode);
        if (idcode != 'h00000DB3)
            $fatal(1, "@%t | [JTAG] Unexpected ID code: expected 0x%h, got 0x%h!",
                $time, 'h00000DB3, idcode);
        // Activate, wait for debug module
        jtag_write(dm::DMControl, dmcontrol);
        do jtag_dbg.read_dmi_exp_backoff(dm::DMControl, dmcontrol);
        while (~dmcontrol.dmactive);
        // Activate, wait for system bus
        jtag_write(dm::SBCS, JtagInitSbcs, 0, 1);
        jtag_write(dm::SBAddress1, '0); // 32-bit addressing only
        $display("@%t | [JTAG] Initialization success", $time);
    endtask

    task automatic jtag_write(
        input dm::dm_csr_e addr,
        input logic [31:0] data,
        input bit wait_cmd = 0,
        input bit wait_sba = 0
    );
        jtag_dbg.write_dmi(addr, data);
    endtask

    task automatic jtag_read_reg32(
        input logic [31:0] addr,
        output logic [31:0] data,
        input bit display_read = 1'b0,
        input int unsigned idle_cycles = 10
    );
        automatic dm::sbcs_t sbcs = dm::sbcs_t'{sbreadonaddr: 1'b1, sbaccess: 2, default: '0};
        jtag_write(dm::SBCS, sbcs, 0, 1);
        jtag_write(dm::SBAddress0, addr[31:0]);
        jtag_dbg.wait_idle(idle_cycles);
        jtag_dbg.read_dmi_exp_backoff(dm::SBData0, data);
        if (display_read)
            $display("@%t | [JTAG] Read 0x%h from 0x%h", $time, data, addr);
    endtask

    task automatic jtag_write_reg32(
        input logic [31:0] addr,
        input logic [31:0] data,
        input bit check_write = 1'b0,
        input int unsigned idle_cycles = 10
    );
        automatic dm::sbcs_t sbcs = dm::sbcs_t'{sbaccess: 2, default: '0};
        $display("@%t | [JTAG] Writing 0x%h to 0x%h", $time, data, addr);
        jtag_write(dm::SBCS, sbcs, 0, 1);
        jtag_write(dm::SBAddress0, addr);
        jtag_write(dm::SBData0, data);
        jtag_dbg.wait_idle(idle_cycles);
        if (check_write) begin
            logic [31:0] rdata;
            jtag_read_reg32(addr, rdata);
            if (rdata !== data) $fatal(1,"@%t | [JTAG] Read back incorrect data 0x%h!", $time,
                rdata);
            else $display("@%t | [JTAG] Read back correct data", $time);
        end
    endtask

    // Halt the core
    task automatic jtag_halt;
      dm::dmstatus_t status;
      // Halt hart 0
      jtag_write(dm::DMControl, dm::dmcontrol_t'{haltreq: 1, dmactive: 1, default: '0});
      $display("@%t | [JTAG] Halting hart 0... ", $time);
      do jtag_dbg.read_dmi_exp_backoff(dm::DMStatus, status);
      while (~status.allhalted);
      $display("@%t | [JTAG] Halted", $time);
    endtask

    // #######################################################################################
    // # Testbench                                                                           #
    // #######################################################################################

    task automatic dispatch_threads(
        input int unsigned pc,
        input int unsigned dp_addr,
        input int unsigned tblock_size,
        input int unsigned number_of_tblocks,
        input int unsigned tgroup_id
    );
        jtag_write_reg32('hFFFFFF00, pc, 1'b1);
        jtag_write_reg32('hFFFFFF04, dp_addr, 1'b1);
        jtag_write_reg32('hFFFFFF08, number_of_tblocks, 1'b1);
        jtag_write_reg32('hFFFFFF0C, tgroup_id, 1'b1);
        jtag_write_reg32('hFFFFFF10, tblock_size, 1'b1);

        // Start dispatch
        jtag_write_reg32('hFFFFFF14, InorderExecution ? 1 : 0, 1'b0);
    endtask

    task automatic dispatch_status(
        output logic finished
    );
        logic [31:0] status;

        jtag_read_reg32('hFFFFFF14, status);

        $display("@%t | [DISPATCH] Status: Start Dispatch: %d Running: %d Finished %d Inorder %d",
            $time, status[0], status[1], status[2], status[3]);
        $display("@%t | [DISPATCH] Finished Threads: %d", $time,
            status[8+3:4]);
        $display("@%t | [DISPATCH] Dispatched Threads: %d", $time,
            status[31:32-8]);

        finished = status[2];
    endtask

    int TblocksToLaunch;
    int TblockSize;
    int DataPerMatrix;
    int unsigned prog [$];

    if (Benchmark == "add_2") begin : gen_add_2
        // 2x2 matrix addition, 1 tblock, 1 thread per tblock
        initial begin
            TblocksToLaunch = 1;
            TblockSize = 1;
            DataPerMatrix = 2 ** 2;
            prog = {
                'h46000000,
                'h46010001,
                'h46020002,
                'h0C030000,
                'h0C040001,
                'h0C050002,
                'h0C060003,
                'h12070302,
                'h04070107,
                'h42080707,
                'h12070402,
                'h04070107,
                'h42090707,
                'h12070502,
                'h04070107,
                'h420A0707,
                'h12070602,
                'h04070107,
                'h42010707,
                'h12070302,
                'h04070207,
                'h420B0707,
                'h12070402,
                'h04070207,
                'h420C0707,
                'h12070502,
                'h04070207,
                'h420D0707,
                'h12070602,
                'h04070207,
                'h42020707,
                'h12070302,
                'h04070007,
                'h12030402,
                'h04030003,
                'h12040502,
                'h04040004,
                'h12050602,
                'h04050005,
                'h0400080B,
                'h0406090C,
                'h04080A0D,
                'h04090102,
                'h45070700,
                'h45030306,
                'h45040408,
                'h45050509,
                'hBF000000
            };
        end
    end : gen_add_2
    else if (Benchmark == "add_4") begin : gen_add_4
        // 4x4 matrix addition, 1 tblock, 4 threads per tblock
        initial begin
            TblocksToLaunch = 1;
            TblockSize = 4;
            DataPerMatrix = 4 ** 2;
            prog = {
                'h46000000,
                'h46010001,
                'h46020002,
                'h0C030001,
                'h0C040002,
                'h0C050003,
                'h0C060004,
                'h00070000,
                'h0B080706,
                'h04060803,
                'h12030602,
                'h04030103,
                'h42070303,
                'h04030804,
                'h12040302,
                'h04040104,
                'h42090404,
                'h04040805,
                'h12050402,
                'h04050105,
                'h420A0505,
                'h12050802,
                'h04050105,
                'h42010505,
                'h12050602,
                'h04050205,
                'h420B0505,
                'h12050302,
                'h04050205,
                'h420C0505,
                'h12050402,
                'h04050205,
                'h420D0505,
                'h12050802,
                'h04050205,
                'h42020505,
                'h12050602,
                'h04050005,
                'h12060302,
                'h04060006,
                'h12030402,
                'h04030003,
                'h12040802,
                'h04040004,
                'h0400070B,
                'h0407090C,
                'h04080A0D,
                'h04090102,
                'h45050500,
                'h45060607,
                'h45030308,
                'h45040409,
                'hBF000000
            };
        end
    end : gen_add_4
    else if (Benchmark == "add_8") begin : gen_add_8
        // 8x8 matrix addition, 4 tblock, 4 threads per tblock
        initial begin
            TblocksToLaunch = 4;
            TblockSize = 4;
            DataPerMatrix = 8 ** 2;
            prog = {
                'h46000000,
                'h46010001,
                'h46020002,
                'h0C030001,
                'h0C040002,
                'h0C050003,
                'h0C060004,
                'h0C070010,
                'h02080000,
                'h00090000,
                'h0B0A0807,
                'h0B070906,
                'h04060A07,
                'h04070603,
                'h12030702,
                'h04030103,
                'h42080303,
                'h04030604,
                'h12040302,
                'h04040104,
                'h42090404,
                'h04040605,
                'h12050402,
                'h04050105,
                'h420A0505,
                'h12050602,
                'h04050105,
                'h42010505,
                'h12050702,
                'h04050205,
                'h420B0505,
                'h12050302,
                'h04050205,
                'h420C0505,
                'h12050402,
                'h04050205,
                'h420D0505,
                'h12050602,
                'h04050205,
                'h42020505,
                'h12050702,
                'h04050005,
                'h12070302,
                'h04070007,
                'h12030402,
                'h04030003,
                'h12040602,
                'h04040004,
                'h0400080B,
                'h0406090C,
                'h04080A0D,
                'h04090102,
                'h45050500,
                'h45070706,
                'h45030308,
                'h45040409,
                'hBF000000
            };
        end
    end : gen_add_8
    else if (Benchmark == "add_16") begin : gen_add_16
        // 16x16 matrix addition, 16 tblock, 4 threads per tblock
        initial begin
            TblocksToLaunch = 16;
            TblockSize = 4;
            DataPerMatrix = 16 ** 2;
            prog = {
                'h46000000,
                'h46010001,
                'h46020002,
                'h0C030001,
                'h0C040002,
                'h0C050003,
                'h0C060004,
                'h0C070010,
                'h02080000,
                'h00090000,
                'h0B0A0807,
                'h0B070906,
                'h04060A07,
                'h04070603,
                'h12030702,
                'h04030103,
                'h42080303,
                'h04030604,
                'h12040302,
                'h04040104,
                'h42090404,
                'h04040605,
                'h12050402,
                'h04050105,
                'h420A0505,
                'h12050602,
                'h04050105,
                'h42010505,
                'h12050702,
                'h04050205,
                'h420B0505,
                'h12050302,
                'h04050205,
                'h420C0505,
                'h12050402,
                'h04050205,
                'h420D0505,
                'h12050602,
                'h04050205,
                'h42020505,
                'h12050702,
                'h04050005,
                'h12070302,
                'h04070007,
                'h12030402,
                'h04030003,
                'h12040602,
                'h04040004,
                'h0400080B,
                'h0406090C,
                'h04080A0D,
                'h04090102,
                'h45050500,
                'h45070706,
                'h45030308,
                'h45040409,
                'hBF000000
            };
        end
    end : gen_add_16
    else initial begin
        $fatal(1, "Unsupported benchmark '%s'", Benchmark);
    end

    initial begin : testbench_logic
        logic [31:0] idcode, data;
        logic finished;
        int offset;

        // Wait for reset to be released
        #ClkPeriodJtag;
        wait(jtag_trst_n && rst_n);

        // Start dumping
        $timeformat(-9, 0, "ns", 12);
        $dumpfile("bgpu_soc.vcd");
        $dumpvars();

        // Init JTAG
        jtag_init();

        // Halt the CPU
        jtag_halt();

        // Write program to memory
        offset = 0;
        for (int i = 0; i < prog.size(); i++) begin
            jtag_write_reg32(offset, prog[i], 1'b1);
            offset += 4;
        end

        // Write Data to memory
        for (int j = 0; j < 3; j++) begin
            for (int i = 0; i < DataPerMatrix; i++) begin
                jtag_write_reg32(offset, i + 1, 1'b1);
                offset += 4;
            end
        end

        // Write Parameters to memory
        jtag_write_reg32(offset, prog.size() * 4, 1'b1);
        offset += 4;
        jtag_write_reg32(offset, (prog.size() + DataPerMatrix) * 4, 1'b1);
        offset += 4;
        jtag_write_reg32(offset, (prog.size() + DataPerMatrix * 2) * 4, 1'b1);
        offset += 4;

        // Dispatch some threads
        dispatch_threads('h0, (prog.size() + DataPerMatrix * 3) * 4, TblockSize, TblocksToLaunch,
            'h2);

        while (1) begin
            dispatch_status(finished);
            if (finished) begin
                $display("@%t | [DISPATCH] All threads finished", $time);
                break;
            end
        end

        // Read back results
        offset = prog.size() * 4;
        for (int j = 0; j < 3; j++) begin
            $display("@%t | [RESULTS] Reading back results for matrix %0d", $time, j);
            for (int i = 0; i < DataPerMatrix; i++) begin
                jtag_read_reg32(offset, data);
                $display("@%t | [RESULTS] Result %0d: 0x%h", $time, i, data);
                offset += 4;
            end
        end

        $display("Finished!");
        $dumpflush;
        $finish();
    end : testbench_logic

    initial begin : check_timeout
        // Check for timeout
        repeat(MaxCycles) @(posedge clk);
        $fatal(1, "@%t | [TESTBENCH] Timeout reached, test did not finish in time!", $time);
    end : check_timeout

endmodule : tb_bgpu_soc
