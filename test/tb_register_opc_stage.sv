// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Testbench for Register Operand Collector Stage
module tb_register_opc_stage import bgpu_pkg::*; #(
    // Simulation parameters
    parameter int unsigned MaxSimCycles     = 100000,
    parameter int unsigned WatchdogTimeout  = 1000,
    parameter int unsigned InstsToComplete  = 10000,
    parameter int unsigned MaxMstWaitCycles = 0,
    parameter int unsigned MaxSubWaitCycles = 1,

    // Simulation time parameters
    parameter time ClkPeriod = 10ns,
    parameter time ApplDelay = 1ns,
    parameter time AcqDelay  = 8ns,

    /// Enable bandwidth test mode (makes EUs always ready)
    parameter bit BandwidthTestMode = 1'b0,

    /// Number of instructions to dispatch simultaneously
    parameter int unsigned DispatchWidth = 2,
    /// Number of instructions that can write back simultaneously
    parameter int unsigned WritebackWidth = 1,
    /// Number of inflight instructions per warp
    parameter int unsigned NumTags = 8,
    /// Width of the Program Counter
    parameter int unsigned PcWidth = 32,
    /// Number of warps per compute unit
    parameter int unsigned NumWarps = 8,
    /// Number of threads per warp
    parameter int unsigned WarpWidth = 4,
    /// How many registers can each warp access as operand or destination
    parameter int unsigned RegIdxWidth = 8,
    /// How many operands each instruction can have
    parameter int unsigned OperandsPerInst = 2,
    /// How many Banks are in the register file
    parameter int unsigned NumBanks = 4,
    /// Width of a singled register
    parameter int unsigned RegWidth = OperandsPerInst * RegIdxWidth,
    /// Should the register file banks be dual port?
    parameter bit          DualPortRegisterBanks = 1'b0,
    /// Number of operand collectors
    parameter int unsigned NumOperandCollectors = 6
) ();

    // #######################################################################################
    // # Local Parameters                                                                    #
    // #######################################################################################

    localparam int unsigned TagWidth = $clog2(NumTags);
    localparam int unsigned WidWidth = NumWarps > 1 ? $clog2(NumWarps) : 1;
    localparam int unsigned NumRegistersPerWarp = 1 << RegIdxWidth;

    // #######################################################################################
    // # Type Definitions                                                                    #
    // #######################################################################################

    typedef logic [            WidWidth-1:0] wid_t;
    typedef logic [         RegIdxWidth-1:0] reg_idx_t;
    typedef logic [             PcWidth-1:0] pc_t;
    typedef logic [           WarpWidth-1:0] act_mask_t;
    typedef logic [RegWidth * WarpWidth-1:0] reg_data_t;
    typedef logic [   TagWidth+WidWidth-1:0] iid_t;

    typedef reg_data_t [NumRegistersPerWarp-1:0] reg_per_warp_t;
    typedef reg_per_warp_t [NumWarps-1:0] reg_file_t;
    typedef reg_data_t [OperandsPerInst-1:0] op_data_t;

    typedef logic     [OperandsPerInst-1:0] op_is_reg_t;
    typedef reg_idx_t [OperandsPerInst-1:0] op_idx_t;

    typedef struct packed {
        iid_t       tag;
        pc_t        pc;
        act_mask_t  active_mask;
        inst_t      inst;
        reg_idx_t   dst;
        op_is_reg_t srcs_is_reg;
        op_idx_t    srcs;
    } disp_req_t;

    typedef struct packed {
        iid_t      tag;
        pc_t       pc;
        act_mask_t active_mask;
        inst_t     inst;
        reg_idx_t  dst;
        op_data_t  src_data;
    } eu_req_t;

    typedef struct packed {
        iid_t      tag;
        act_mask_t act_mask;
        reg_idx_t  dst;
        reg_data_t data;
    } eu_rsp_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    logic clk, rst_n, initialized;

    // From Dispatcher
    logic      [DispatchWidth-1:0] opc_ready, disp_valid_mst, disp_valid;
    disp_req_t [DispatchWidth-1:0] disp_req;

    iid_t       [DispatchWidth-1:0] disp_req_tag;
    pc_t        [DispatchWidth-1:0] disp_req_pc;
    act_mask_t  [DispatchWidth-1:0] disp_req_active_mask;
    inst_t      [DispatchWidth-1:0] disp_req_inst;
    reg_idx_t   [DispatchWidth-1:0] disp_req_dst;
    op_is_reg_t [DispatchWidth-1:0] disp_req_srcs_is_reg;
    op_idx_t    [DispatchWidth-1:0] disp_req_srcs;

    // To Execution units
    logic [DispatchWidth-1:0] opc_valid, eu_ready, eu_ready_sub;
    eu_req_t [DispatchWidth-1:0] eu_req;

    iid_t      [DispatchWidth-1:0] eu_req_tag;
    pc_t       [DispatchWidth-1:0] eu_req_pc;
    act_mask_t [DispatchWidth-1:0] eu_req_active_mask;
    inst_t     [DispatchWidth-1:0] eu_req_inst;
    reg_idx_t  [DispatchWidth-1:0] eu_req_dst;
    op_data_t  [DispatchWidth-1:0] eu_req_src_data;

    // From Execution units
    logic opc_to_eu_ready, eu_valid;
    eu_rsp_t eu_rsp;

    // Register file contents
    reg_file_t reg_file;

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
    // # Dispatcher Interface Master                                                         #
    // #######################################################################################

    for (genvar didx = 0; didx < DispatchWidth; didx++) begin : gen_dispatcher_mst
        rand_stream_mst #(
            .data_t       ( disp_req_t       ),
            .ApplDelay    ( ApplDelay        ),
            .AcqDelay     ( AcqDelay         ),
            .MinWaitCycles( 0                ),
            .MaxWaitCycles( MaxMstWaitCycles )
        ) i_dispatcher_mst (
            .clk_i ( clk   ),
            .rst_ni( rst_n ),

            .valid_o( disp_valid_mst[didx] ),
            .ready_i( opc_ready     [didx] ),
            .data_o ( disp_req      [didx] )
        );

        stream_watchdog #(
            .NumCycles( WatchdogTimeout )
        ) i_dispatcher_watchdog (
            .clk_i ( clk   ),
            .rst_ni( rst_n ),

            .valid_i( disp_valid_mst[didx] ),
            .ready_i( opc_ready     [didx] )
        );

        assign disp_valid          [didx] = disp_valid_mst[didx] && initialized;
        assign disp_req_tag        [didx] = disp_req[didx].tag;
        assign disp_req_pc         [didx] = disp_req[didx].pc;
        assign disp_req_active_mask[didx] = disp_req[didx].active_mask;
        assign disp_req_inst       [didx] = disp_req[didx].inst;
        assign disp_req_dst        [didx] = disp_req[didx].dst;
        assign disp_req_srcs_is_reg[didx] = disp_req[didx].srcs_is_reg;
        assign disp_req_srcs       [didx] = disp_req[didx].srcs;
    end : gen_dispatcher_mst

    // #######################################################################################
    // # Execution Units                                                                     #
    // #######################################################################################

    for (genvar didx = 0; didx < DispatchWidth; didx++) begin : gen_eu
        rand_stream_slv #(
            .data_t       ( eu_req_t         ),
            .ApplDelay    ( ApplDelay        ),
            .AcqDelay     ( AcqDelay         ),
            .MinWaitCycles( 1                ),
            .MaxWaitCycles( MaxSubWaitCycles ),
            .Enqueue      ( 1'b0             )
        ) i_eu_sub (
            .clk_i ( clk   ),
            .rst_ni( rst_n ),

            .data_i ( eu_req      [didx] ),
            .valid_i( opc_valid   [didx] ),
            .ready_o( eu_ready_sub[didx] )
        );

        stream_watchdog #(
            .NumCycles( WatchdogTimeout )
        ) i_eu_watchdog (
            .clk_i  ( clk                  ),
            .rst_ni ( rst_n && initialized ),
            .valid_i( opc_valid   [didx]   ),
            .ready_i( eu_ready_sub[didx]   )
        );

        assign eu_ready[didx]             = eu_ready_sub[didx] || BandwidthTestMode;
        assign eu_req  [didx].tag         = eu_req_tag        [didx];
        assign eu_req  [didx].pc          = eu_req_pc         [didx];
        assign eu_req  [didx].active_mask = eu_req_active_mask[didx];
        assign eu_req  [didx].inst        = eu_req_inst       [didx];
        assign eu_req  [didx].dst         = eu_req_dst        [didx];
        assign eu_req  [didx].src_data    = eu_req_src_data   [didx];
    end : gen_eu

    // #######################################################################################
    // # DUT                                                                                 #
    // #######################################################################################

    register_opc_stage #(
        .DispatchWidth        ( DispatchWidth         ),
        .WritebackWidth       ( WritebackWidth        ),
        .NumTags              ( NumTags               ),
        .PcWidth              ( PcWidth               ),
        .NumWarps             ( NumWarps              ),
        .WarpWidth            ( WarpWidth             ),
        .RegIdxWidth          ( RegIdxWidth           ),
        .OperandsPerInst      ( OperandsPerInst       ),
        .NumBanks             ( NumBanks              ),
        .RegWidth             ( RegWidth              ),
        .DualPortRegisterBanks( DualPortRegisterBanks ),
        .NumOperandCollectors ( NumOperandCollectors  )
    ) i_register_opc_stage (
        // Clock and reset
        .clk_i ( clk   ),
        .rst_ni( rst_n ),

        // Dispatcher interface
        .opc_ready_o      ( opc_ready            ),
        .disp_valid_i     ( disp_valid           ),
        .disp_tag_i       ( disp_req_tag         ),
        .disp_pc_i        ( disp_req_pc          ),
        .disp_act_mask_i  ( disp_req_active_mask ),
        .disp_inst_i      ( disp_req_inst        ),
        .disp_dst_i       ( disp_req_dst         ),
        .disp_src_is_reg_i( disp_req_srcs_is_reg ),
        .disp_src_i       ( disp_req_srcs        ),

        // To Execution units
        .opc_valid_o       ( opc_valid          ),
        .eu_ready_i        ( eu_ready           ),
        .opc_tag_o         ( eu_req_tag         ),
        .opc_pc_o          ( eu_req_pc          ),
        .opc_act_mask_o    ( eu_req_active_mask ),
        .opc_inst_o        ( eu_req_inst        ),
        .opc_dst_o         ( eu_req_dst         ),
        .opc_operand_data_o( eu_req_src_data    ),

        // From Execution units
        .opc_to_eu_ready_o( opc_to_eu_ready ),
        .eu_valid_i       ( eu_valid        ),
        .eu_act_mask_i    ( eu_rsp.act_mask ),
        .eu_tag_i         ( eu_rsp.tag      ),
        .eu_dst_i         ( eu_rsp.dst      ),
        .eu_data_i        ( eu_rsp.data     )
    );

    // ########################################################################################
    // # Simulation Logic                                                                     #
    // ########################################################################################

    disp_req_t disp_requests[$];
    eu_req_t   eu_requests  [$];

    initial begin : acquire_block
        forever begin
            @(posedge clk);
            for (int didx = 0; didx < DispatchWidth; didx++) begin
                if (opc_ready[didx] && disp_valid[didx]) begin
                    // Add dispatch request to the queue
                    disp_requests.push_back(disp_req[didx]);
                    $display("Disp req %d: Tag %0h, PC %0h, Act Mask %b, Dst %0d, Inst %0h, Req %b",
                        didx, disp_req[didx].tag, disp_req[didx].pc, disp_req[didx].active_mask,
                        disp_req[didx].dst, disp_req[didx].inst, disp_req[didx].srcs_is_reg);
                end

                if (opc_valid[didx] && eu_ready[didx]) begin
                    // Add to EU requests
                    eu_requests.push_back(eu_req[didx]);
                    $display("EU req %d: Tag %0h, PC %0h, Act Mask %b, Dst %0d, Inst %0h, Data %h",
                        didx, eu_req[didx].tag, eu_req[didx].pc, eu_req[didx].active_mask,
                        eu_req[didx].dst, eu_req[didx].inst, eu_req[didx].src_data);
                end
            end
        end
    end : acquire_block

    // Check if dispatched instruction and instruction sent to Execution Unit match
    initial begin : check_disp_req_match
        disp_req_t   disp;
        eu_req_t     eu;
        logic        found;
        int unsigned wid;
        int unsigned reg_idx;
        int unsigned test;

        forever begin
            @(posedge clk);
            while (disp_requests.size() > 0 && eu_requests.size() > 0) begin
                // Get newest eu request
                eu = eu_requests.pop_front();

                // Search for matching dispatch request
                found = 1'b0;
                foreach (disp_requests[i]) begin
                    disp = disp_requests[i];
                    if (disp.tag == eu.tag
                        && disp.pc == eu.pc
                        && disp.active_mask == eu.active_mask
                        && disp.dst == eu.dst
                        && disp.inst == eu.inst) begin

                        for (int j = 0; j < OperandsPerInst; j++) begin
                            if (!disp.srcs_is_reg[j]) begin
                                continue; // Skip if the source is not required
                            end

                            wid = 0;
                            reg_idx = 0;

                            if (NumWarps > 1)
                                wid[WidWidth-1:0] = eu.tag[WidWidth-1:0];

                            reg_idx[RegIdxWidth-1:0] = disp.srcs[j];

                            if (eu.src_data[j] != reg_file[wid][reg_idx]) begin
                                $display("Mismatch in source data for operand %0d", j);
                                $error("Expected: %0h, Got: %0h",
                                    reg_file[wid][reg_idx], eu.src_data[j]);
                            end else begin
                                $display("Source data for operand %0d: %0d == %0d", j,
                                    eu.src_data[j], reg_file[wid][reg_idx]);
                            end
                        end

                        disp_requests.delete(i);
                        found = 1'b1;
                        break;
                    end
                end

                assert (found)
                else $error("No matching disp request found for Execution Unit request tag %0h!",
                    eu.tag);
            end
        end
    end : check_disp_req_match

    function static reg_data_t randomize_ram_data();
        int unsigned rand_data;
        reg_data_t data_o;

        if (RegWidth * WarpWidth <= 32) begin
            // If the data width is less than or equal to 32 bits, randomize the entire data_o.
            rand_data = $urandom;
            /* verilator lint_off SELRANGE */
            data_o = rand_data[RegWidth * WarpWidth - 1:0];
            /* verilator lint_on SELRANGE */
        end else begin
            /* verilator lint_off UNSIGNED */
            for (int i = 0; i <= (RegWidth * WarpWidth + RegWidth * WarpWidth / 2) / 32; i++) begin
            /* verilator lint_on UNSIGNED */
                rand_data = $urandom;
                /* verilator lint_off SELRANGE */
                data_o[i*32+:32] = rand_data;
                /* verilator lint_on SELRANGE */
            end
        end

        return data_o;
    endfunction

    initial begin : simulation_logic
        int unsigned cycles, dispatched_insts, insts_sent_to_eu;

        int unsigned dispatched_insts_per_port[DispatchWidth];
        int unsigned insts_sent_to_eu_per_port[DispatchWidth];

        int unsigned dispatched_per_opc     [NumOperandCollectors];
        int unsigned insts_completed_per_opc[NumOperandCollectors];
        int unsigned read_stalls_per_opc    [NumOperandCollectors];
        int unsigned dispatched_insts_sum, insts_completed_insts_sum, read_stalls_sum;

        for (int i = 0; i < NumOperandCollectors; i++) begin
            dispatched_per_opc     [i] = 0;
            insts_completed_per_opc[i] = 0;
            read_stalls_per_opc    [i] = 0;
        end

        initialized = 1'b0;

        cycles = 0;
        dispatched_insts = 0;
        insts_sent_to_eu = 0;

        dispatched_insts_per_port = '{default: 0};
        insts_sent_to_eu_per_port = '{default: 0};

        disp_requests = {};
        eu_requests   = {};

        $timeformat(-9, 0, "ns", 12);
        // configure VCD dump
        $dumpfile("register_opc_stage.vcd");
        $dumpvars();

        $display("Initializing registers...");
        eu_valid = 1'b0;
        eu_rsp   = '{default: 0};
        @(posedge clk);
        @(posedge clk);
        while (!rst_n) begin
            @(posedge clk);
        end

        for (int wid = 0; wid < NumWarps; wid++) begin
            for (int reg_idx = 0; reg_idx < (1 << RegIdxWidth); reg_idx++) begin
                #ApplDelay;
                eu_valid = 1'b1;
                eu_rsp.tag[WidWidth-1:0] = wid[WidWidth-1:0];
                eu_rsp.dst               = reg_idx[RegIdxWidth-1:0];
                eu_rsp.act_mask          = '1; // Write all threads

                reg_file[wid][reg_idx]   = randomize_ram_data();
                eu_rsp.data              = reg_file[wid][reg_idx];
                @(posedge clk);
                while (!opc_to_eu_ready) begin
                    @(posedge clk);
                end
            end
        end
        #ApplDelay;
        eu_valid    = 1'b0;
        @(posedge clk);
        #ApplDelay;
        initialized = 1'b1;

        $display("Starting simulation!");

        while (cycles < MaxSimCycles && insts_sent_to_eu < InstsToComplete) begin
            // Wait for clock edge
            @(posedge clk);
            cycles++;

            for (int didx = 0; didx < DispatchWidth; didx++) begin
                // Instruction dispatch
                if (disp_valid[didx] && opc_ready[didx]) begin
                    dispatched_insts++;
                    dispatched_insts_per_port[didx]++;
                    $display("Cycle %0d: Dispatching instruction %d", cycles, didx);
                    $display("\tTag: %0h", disp_req[didx].tag);
                    $display("\tPC: %0h", disp_req[didx].pc);
                    $display("\tActive Mask: %b", disp_req[didx].active_mask);
                    $display("\tInstruction: %0h", disp_req[didx].inst);
                    $display("\tDst reg: %0d", disp_req[didx].dst);
                    for (int i = 0; i < OperandsPerInst; i++) begin
                        $display("\tSrc[%0d] req: %0b reg: %0d", i, disp_req[didx].srcs_is_reg[i],
                            disp_req[didx].srcs[i]);
                    end
                end

                // To Execution units
                if (opc_valid[didx] && eu_ready[didx]) begin
                    insts_sent_to_eu++;
                    insts_sent_to_eu_per_port[didx]++;
                    $display("Cycle %0d: Sending instruction to Execution Unit %d", cycles, didx);
                    $display("\tTag: %0h", eu_req[didx].tag);
                    $display("\tTag (wid): %0h", eu_req[didx].tag[WidWidth-1:0]);
                    $display("\tPC: %0h", eu_req[didx].pc);
                    $display("\tActive Mask: %b", eu_req[didx].active_mask);
                    $display("\tInstruction: %0h", eu_req[didx].inst);
                    $display("\tDst reg: %0d", eu_req[didx].dst);
                    for (int i = 0; i < OperandsPerInst; i++) begin
                        $display("\tSrc[%0d] data: %0h", i, eu_req[didx].src_data[i]);
                    end
                end
            end

            for (int i = 0; i < NumOperandCollectors; i++) begin
                if (i_register_opc_stage.opc_insert_valid[i]
                        && i_register_opc_stage.opc_insert_ready[i]) begin
                    dispatched_per_opc[i]++;
                    $display("Cycle %0d: Inserting instruction into Operand Collector %0d", cycles,
                        i);
                end
                if (i_register_opc_stage.opc_eu_ready[i]
                    && i_register_opc_stage.rr_opc_valid[0][i]
                ) begin
                    insts_completed_per_opc[i]++;
                    $display("Cycle %0d: Operand Collector %0d is sending instruction to EU",
                        cycles, i);
                end

                for (int j = 0; j < OperandsPerInst; j++) begin
                    if (i_register_opc_stage.opc_read_req_valid[i * OperandsPerInst + j]
                        && !i_register_opc_stage.opc_read_req_ready[i * OperandsPerInst + j]
                    ) begin
                        read_stalls_per_opc[i]++;
                        $display("Cycle %0d: Operand Collector %0d has a read stall for operand %0d"
                            , cycles, i, j);
                    end
                end
            end
        end

        $dumpflush;
        $display("\nSimulation finished after %0d cycles.\n", cycles);

        wait(eu_requests.size() == 0);

        assert (dispatched_insts > 0)
        else $error("No instructions were dispatched during the simulation!");

        assert (insts_sent_to_eu > 0)
        else $error("No instructions were sent to the Execution Units during the simulation!");

        for (int i = 0; i < DispatchWidth; i++) begin
            $display("Dispatched %0d instructions on port %0d", dispatched_insts_per_port[i], i);
            $display("Sent %0d instructions to Execution Units on port %0d",
                insts_sent_to_eu_per_port[i], i);

            assert (dispatched_insts_per_port[i] > 0)
            else $warning("No instructions were dispatched on port %0d!", i);

            assert (insts_sent_to_eu_per_port[i] > 0)
            else $warning("No instructions were sent to Execution Units on port %0d!", i);
        end

        dispatched_insts_sum = 0;
        insts_completed_insts_sum = 0;
        read_stalls_sum = 0;
        for (int i = 0; i < NumOperandCollectors; i++) begin
            $display("Operand Collector %0d dispatched %0d instructions", i, dispatched_per_opc[i]);
            $display("Operand Collector %0d sent %0d instructions to Execution Units", i,
                insts_completed_per_opc[i]);
            $display("Operand Collector %0d had %0d read stalls", i, read_stalls_per_opc[i]);

            assert (dispatched_per_opc[i] > 0)
            else $warning("Operand Collector %0d did not dispatch any instructions!", i);
            assert (insts_completed_per_opc[i] > 0)
            else $warning("Operand Collector %0d did not send any instructions to Execution Units!",
                i);

            dispatched_insts_sum      += dispatched_per_opc     [i];
            insts_completed_insts_sum += insts_completed_per_opc[i];
            read_stalls_sum           += read_stalls_per_opc    [i];
        end

        assert (dispatched_insts_sum == dispatched_insts)
        else $error("The total number of dispatched instructions does not match the sum of",
            " per-collector counts!");

        assert (insts_completed_insts_sum == insts_sent_to_eu)
        else $error("The total number of instructions sent to Execution Units does not match the",
            " sum of per-collector counts!");

        $display("Dispatched %0d instructions", dispatched_insts);
        $display("Sent %0d instructions to Execution Units", insts_sent_to_eu);
        $display("Total read stalls across all Operand Collectors: %0d", read_stalls_sum);

        assert (insts_sent_to_eu >= dispatched_insts - NumOperandCollectors)
        else $error("Not all dispatched instructions were sent to the Execution Units!");

        assert (cycles < MaxSimCycles)
        else $error("Simulation exceeded maximum cycle count of %0d!", MaxSimCycles);

        assert (insts_sent_to_eu == InstsToComplete)
        else $error("The number of instructions to complete was not reached!");

        $finish;
    end : simulation_logic

endmodule : tb_register_opc_stage
