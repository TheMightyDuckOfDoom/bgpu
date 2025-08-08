// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "common_cells/registers.svh"

/// BGPU SoC top-level module testbench
module tb_bgpu_soc #(
    /// Width of the data bus to the memory controller
    parameter int unsigned MctrlWidth = 256,
    /// Width of the addressable physical memory by the memory controller
    parameter int unsigned MctrlAddressWidth = 16,

    parameter time ClkPeriodJtag  = 50ns,
    parameter time ClkPeriod      = 10ns,
    parameter time ClkPeriodMctrl = 5ns,

    parameter time ApplyDelay = 1ns,
    parameter time AcqDelay   = 0.9ns,

    parameter int unsigned MaxCycles = 1000000
) ();
    // #######################################################################################
    // # Local Parameters                                                                    #
    // #######################################################################################

    // #######################################################################################
    // # Type Definitions                                                                    #
    // #######################################################################################

    typedef logic [MctrlAddressWidth-1:0] mctrl_addr_t;
    typedef logic [     MctrlWidth/8-1:0] mctrl_mask_t;
    typedef logic [       MctrlWidth-1:0] mctrl_data_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Clock and Reset
    logic clk, rst_n;

    // JTAG Interface
    logic jtag_tck, jtag_tdi, jtag_tdo, jtag_tms, jtag_trst_n;

    // Command
    logic        mctrl_cmd_ready, mctrl_cmd_valid, mctrl_cmd_read;
    mctrl_addr_t mctrl_cmd_addr;

    // Write Data
    logic        mctrl_wdata_ready, mctrl_wdata_valid;
    mctrl_data_t mctrl_wdata;
    mctrl_mask_t mctrl_wmask;

    // Read Data
    logic        mctrl_rdata_valid;
    mctrl_data_t mctrl_rdata;

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
        .ClkPeriod   ( ClkPeriodJtag ),
        .RstClkCycles( 3             )
    ) i_clk_jtag_rst_gen (
        .clk_o ( jtag_tck    ),
        .rst_no( jtag_trst_n )
    );

    // #######################################################################################
    // # DUT                                                                                 #
    // #######################################################################################

    bgpu_soc #(
        .MctrlWidth       ( MctrlWidth        ),
        .MctrlAddressWidth( MctrlAddressWidth )
    ) i_bgpu (
        .clk_i ( clk   ),
        .rst_ni( rst_n ),

        .testmode_i( 1'b0 ),

        .jtag_tck_i  ( jtag_tck    ),
        .jtag_tdi_i  ( jtag_tdi    ),
        .jtag_tdo_o  ( jtag_tdo    ),
        .jtag_tms_i  ( jtag_tms    ),
        .jtag_trst_ni( jtag_trst_n ),

        .mctrl_cmd_ready_i( mctrl_cmd_ready ),
        .mctrl_cmd_valid_o( mctrl_cmd_valid ),
        .mctrl_cmd_read_o ( mctrl_cmd_read  ),
        .mctrl_cmd_addr_o ( mctrl_cmd_addr  ),

        .mctrl_wdata_ready_i( mctrl_wdata_ready ),
        .mctrl_wdata_valid_o( mctrl_wdata_valid ),
        .mctrl_wdata_o      ( mctrl_wdata       ),
        .mctrl_wmask_o      ( mctrl_wmask       ),

        .mctrl_rdata_valid_i( mctrl_rdata_valid ),
        .mctrl_rdata_i      ( mctrl_rdata       )
    );

    // #######################################################################################
    // # Memory Controller                                                                   #
    // #######################################################################################

    assign mctrl_cmd_ready   = 1'b1;
    assign mctrl_wdata_ready = 1'b1;

    tc_sram #(
        .NumWords   ( 1 << (MctrlAddressWidth - $clog2(MctrlWidth / 8)) ),
        .DataWidth  ( MctrlWidth    ),
        .ByteWidth  ( 8             ),
        .NumPorts   ( 1             ),
        .Latency    ( 1             ),
        .SimInit    ( "zeros"       ),
        .PrintSimCfg( 1'b1          ),
        .ImplKey    ( "i_mctrl_mem" )
    ) i_mctlr_mem (
        .clk_i ( clk   ),
        .rst_ni( rst_n ),

        .req_i  ( mctrl_cmd_valid ),
        .we_i   ( !mctrl_cmd_read ),

        .addr_i ( mctrl_cmd_addr[MctrlAddressWidth-1:$clog2(MctrlWidth / 8)] ),

        .wdata_i( mctrl_wdata_valid ? mctrl_wdata : '0 ),
        .be_i   ( mctrl_wdata_valid ? mctrl_wmask : '0 ),

        .rdata_o( mctrl_rdata )
    );

    assert property (@(posedge clk) disable iff (!rst_n)
        mctrl_cmd_valid |-> mctrl_cmd_addr[$clog2(MctrlWidth / 8) - 1:0] == '0
    ) else $fatal(1, "@%t | [Memory Controller] Address must be aligned to %0d bytes!",
        $time, MctrlWidth / 8);

    `FF(mctrl_rdata_valid, mctrl_cmd_valid && mctrl_cmd_read, 1'b0, clk, rst_n)

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
        // if (wait_cmd) begin
        //     dm::abstractcs_t acs;
        //     do begin
        //         jtag_dbg.read_dmi_exp_backoff(dm::AbstractCS, acs);
        //         if (acs.cmderr != '0) $fatal(1, "[JTAG] Abstract command error!");
        //     end while (acs.busy);
        // end
        // if (wait_sba) begin
        //     dm::sbcs_t sbcs;
        //     do begin
        //         jtag_dbg.read_dmi_exp_backoff(dm::SBCS, sbcs);
        //         // if (sbcs.sberror != '0) $error("[JTAG] System bus error!");
        //         // if ((sbcs.sberror != '0) || sbcs.sbbusyerror) $error("[JTAG] System bus error!");
        //     end while (sbcs.sbbusy);
        // end
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
        input int unsigned number_of_tblocks,
        input int unsigned tgroup_id
    );
        jtag_write_reg32('hFFFFFF00, pc, 1'b1);
        jtag_write_reg32('hFFFFFF04, dp_addr, 1'b1);
        jtag_write_reg32('hFFFFFF08, number_of_tblocks, 1'b1);
        jtag_write_reg32('hFFFFFF0C, tgroup_id, 1'b1);

        // Start dispatch
        jtag_write_reg32('hFFFFFF10, 0, 1'b0);
    endtask

    task automatic dispatch_status(
        output logic finished
    );
        logic [31:0] status;

        jtag_read_reg32('hFFFFFF10, status);

        $display("@%t | [DISPATCH] Status: Start Dispatch: %d Running: %d Finished %d", $time,
            status[0], status[1], status[2]);
        $display("@%t | [DISPATCH] Finished Threads: %d", $time,
            status[8+3:4]);
        $display("@%t | [DISPATCH] Dispatched Threads: %d", $time,
            status[31:32-8]);

        finished = status[2];
    endtask

    // 2x2 matrix addition, 1 tblock
    // int TblocksToLaunch = 1;
    // int DataPerMatrix = 2 ** 2;
    // int unsigned prog [$] = {
    //     'h04000000,
    //     'h42010000,
    //     'h0c020004,
    //     'h42020200,
    //     'h0c000008,
    //     'h42000000,
    //     'h0c030200,
    //     'h42030300,
    //     'h0c040204,
    //     'h42040400,
    //     'h0c050208,
    //     'h42050500,
    //     'h0c02020c,
    //     'h42020200,
    //     'h0c060000,
    //     'h42060600,
    //     'h0c070004,
    //     'h42070700,
    //     'h0c080008,
    //     'h42080800,
    //     'h0c00000c,
    //     'h42000000,
    //     'h0c090100,
    //     'h0c0a0104,
    //     'h0c0b0108,
    //     'h0c01010c,
    //     'h05030306,
    //     'h45090903,
    //     'h05030407,
    //     'h450a0a03,
    //     'h05030508,
    //     'h450b0b03,
    //     'h05000200,
    //     'h45010100,
    //     'hff000000,
    //     'hff000000
    // };

    // 4x4 matrix addition, 1 tblock
    // int TblocksToLaunch = 1;
    // int DataPerMatrix = 4 ** 2;
    // int unsigned prog [$] = {
    //     'h04000000,
    //     'h42010000,
    //     'h0c020004,
    //     'h42020200,
    //     'h0c030008,
    //     'h42030300,
    //     'h00000000,
    //     'h0e040002,
    //     'h0e050402,
    //     'h05050205,
    //     'h42060500,
    //     'h0e050402,
    //     'h05050305,
    //     'h42070500,
    //     'h0c050401,
    //     'h0e080502,
    //     'h05080208,
    //     'h42090800,
    //     'h0e080502,
    //     'h05080308,
    //     'h420a0800,
    //     'h0c080402,
    //     'h0e0b0802,
    //     'h050b020b,
    //     'h420c0b00,
    //     'h0e0b0802,
    //     'h050b030b,
    //     'h420d0b00,
    //     'h0c0b0403,
    //     'h0e0e0b02,
    //     'h050e020e,
    //     'h42020e00,
    //     'h0e0e0b02,
    //     'h050e030e,
    //     'h42030e00,
    //     'h0e0e0502,
    //     'h050e010e,
    //     'h0e050802,
    //     'h05050105,
    //     'h0e080b02,
    //     'h05080108,
    //     'h0e0b0402,
    //     'h050b010b,
    //     'h0501090a,
    //     'h450e0e01,
    //     'h05010c0d,
    //     'h45050501,
    //     'h05010203,
    //     'h45080801,
    //     'h05010607,
    //     'h450b0b01,
    //     'hff000000
    // };

    // 8x8 matrix addition, 4 tblock
    int TblocksToLaunch = 4;
    int DataPerMatrix = 8 ** 2;
    int unsigned prog [$] = {
        'h04000000, // special                   r0, %param
        'h42010000, // ld.int32.param            r1,   r0
        'h0c020004, // add.ri.int32              r2,   r0, 4
        'h42020200, // ld.int32.param            r2,   r2
        'h0c030008, // add.ri.int32              r3,   r0, 8
        'h42030300, // ld.int32.param            r3,   r3
        'h02000000, // special                   r0, %gidx0
        'h00040000, // special                   r4, %lidx0
        'h0e050004, // shl.ri.int32              r5,   r0,    4
        'h0e060402, // shl.ri.int32              r6,   r4,    2
        'h05070506, // add.rr.int32              r7,   r5,   r6
        'h0e050702, // shl.ri.int32              r5,   r7,    2
        'h05050205, // add.rr.int32              r5,   r2,   r5
        'h42060500, // ld.int32.global           r6,   r5
        'h0e050702, // shl.ri.int32              r5,   r7,    2
        'h05050305, // add.rr.int32              r5,   r3,   r5
        'h42080500, // ld.int32.global           r8,   r5
        'h0c050701, // add.ri.int32              r5,   r7,    1
        'h0e090502, // shl.ri.int32              r9,   r5,    2
        'h05090209, // add.rr.int32              r9,   r2,   r9
        'h420a0900, // ld.int32.global          r10,   r9
        'h0e090502, // shl.ri.int32              r9,   r5,    2
        'h05090309, // add.rr.int32              r9,   r3,   r9
        'h420b0900, // ld.int32.global          r11,   r9
        'h0c090702, // add.ri.int32              r9,   r7,    2
        'h0e0c0902, // shl.ri.int32             r12,   r9,    2
        'h050c020c, // add.rr.int32             r12,   r2,  r12
        'h420d0c00, // ld.int32.global          r13,  r12
        'h0e0c0902, // shl.ri.int32             r12,   r9,    2
        'h050c030c, // add.rr.int32             r12,   r3,  r12
        'h420e0c00, // ld.int32.global          r14,  r12
        'h0c0c0703, // add.ri.int32             r12,   r7,    3
        'h0e0f0c02, // shl.ri.int32             r15,  r12,    2
        'h050f020f, // add.rr.int32             r15,   r2,  r15
        'h42020f00, // ld.int32.global           r2,  r15
        'h0e0f0c02, // shl.ri.int32             r15,  r12,    2
        'h050f030f, // add.rr.int32             r15,   r3,  r15
        'h42030f00, // ld.int32.global           r3,  r15
        'h0e0f0502, // shl.ri.int32             r15,   r5,    2
        'h050f010f, // add.rr.int32             r15,   r1,  r15
        'h0e050902, // shl.ri.int32              r5,   r9,    2
        'h05050105, // add.rr.int32              r5,   r1,   r5
        'h0e090c02, // shl.ri.int32              r9,  r12,    2
        'h05090109, // add.rr.int32              r9,   r1,   r9
        'h0e0c0702, // shl.ri.int32             r12,   r7,    2
        'h050c010c, // add.rr.int32             r12,   r1,  r12
        'h05010a0b, // add.rr.int32              r1,  r10,  r11
        'h450f0f01, // st.int32.global          r15,   r1
        'h05010d0e, // add.rr.int32              r1,  r13,  r14
        'h45050501, // st.int32.global           r5,   r1
        'h05010203, // add.rr.int32              r1,   r2,   r3
        'h45090901, // st.int32.global           r9,   r1
        'h05010608, // add.rr.int32              r1,   r6,   r8
        'h450c0c01, // st.int32.global          r12,   r1
        'hff000000  // stop
    };

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
        $dumpvars(1, i_bgpu_soc);

        // Init JTAG
        jtag_init();

        // Halt the CPU
        jtag_halt();

        // Write program to memory
        offset = 0;
        for(int i = 0; i < prog.size(); i++) begin
            jtag_write_reg32(offset, prog[i], 1'b1);
            offset += 4;
        end

        // Write Data to memory
        for(int j = 0; j < 3; j++) begin
            for(int i = 0; i < DataPerMatrix; i++) begin
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
        dispatch_threads('h0, (prog.size() + DataPerMatrix * 3) * 4, TblocksToLaunch, 'h2);

        while(1) begin
            dispatch_status(finished);
            if (finished) begin
                $display("@%t | [DISPATCH] All threads finished", $time);
                break;
            end
        end

        // Read back results
        offset = prog.size() * 4;
        for(int j = 0; j < 3; j++) begin
            $display("@%t | [RESULTS] Reading back results for matrix %0d", $time, j);
            for(int i = 0; i < DataPerMatrix; i++) begin
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
