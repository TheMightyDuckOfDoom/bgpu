// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "bgpu/instructions.svh"

/// Testbench for Register Operand Collector Stage
module tb_register_opc_stage #(
    // Simulation parameters
    parameter int unsigned MaxSimCycles     = 100000,
    parameter int unsigned WatchdogTimeout  = 1000,
    parameter int unsigned InstsToComplete  = 1000,
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
    parameter int unsigned NumWarps = 8,
    /// Number of threads per warp
    parameter int unsigned WarpWidth = 4,
    /// How many registers can each warp access as operand or destination
    parameter int unsigned RegIdxWidth = 6,
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

    typedef struct packed {
        iid_t       tag;
        pc_t        pc;
        act_mask_t  active_mask;
        bgpu_inst_t inst;
        reg_idx_t   dst;
        logic       [OperandsPerInst-1:0] srcs_required;
        reg_idx_t   [OperandsPerInst-1:0] srcs;
    } disp_req_t;

    typedef struct packed {
        iid_t       tag;
        pc_t        pc;
        act_mask_t  active_mask;
        bgpu_inst_t inst;
        reg_idx_t   dst;
        reg_data_t  [OperandsPerInst-1:0] src_data;
    } eu_req_t;

    typedef struct packed {
        iid_t      tag;
        reg_idx_t  dst;
        reg_data_t data;
    } eu_rsp_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    logic clk, rst_n, initialized;

    // From Dispatcher
    logic opc_ready, disp_valid;
    disp_req_t disp_req;

    // To Execution units
    logic opc_valid, eu_ready;
    eu_req_t eu_req;

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

    rand_stream_mst #(
        .data_t       ( disp_req_t       ),
        .ApplDelay    ( ApplDelay        ),
        .AcqDelay     ( AcqDelay         ),
        .MinWaitCycles( 0                ),
        .MaxWaitCycles( MaxMstWaitCycles )
    ) i_dispatcher_mst (
        .clk_i  ( clk        ),
        .rst_ni ( rst_n      ),
        .valid_o( disp_valid ),
        .ready_i( opc_ready  ),
        .data_o ( disp_req   )
    );

    stream_watchdog #(
        .NumCycles( WatchdogTimeout )
    ) i_dispatcher_watchdog (
        .clk_i  ( clk        ),
        .rst_ni ( rst_n      ),
        .valid_i( disp_valid ),
        .ready_i( opc_ready  )
    );

    // #######################################################################################
    // # Execution Units                                                                     #
    // #######################################################################################

    rand_stream_slv #(
        .data_t       ( eu_req_t         ),
        .ApplDelay    ( ApplDelay        ),
        .AcqDelay     ( AcqDelay         ),
        .MinWaitCycles( 1                ),
        .MaxWaitCycles( MaxSubWaitCycles ),
        .Enqueue      ( 1'b0             )
    ) i_eu_sub (
        .clk_i  ( clk       ),
        .rst_ni ( rst_n     ),
        .data_i ( eu_req    ),
        .valid_i( opc_valid ),
        .ready_o( eu_ready  )
    );

    stream_watchdog #(
        .NumCycles( WatchdogTimeout )
    ) i_eu_watchdog (
        .clk_i  ( clk                  ),
        .rst_ni ( rst_n && initialized ),
        .valid_i( opc_valid            ),
        .ready_i( eu_ready             )
    );

    // #######################################################################################
    // # DUT                                                                                 #
    // #######################################################################################

    register_opc_stage #(
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
        .opc_ready_o        ( opc_ready                 ),
        .disp_valid_i       ( disp_valid && initialized ),
        .disp_tag_i         ( disp_req.tag              ),
        .disp_pc_i          ( disp_req.pc               ),
        .disp_act_mask_i    ( disp_req.active_mask      ),
        .disp_inst_i        ( disp_req.inst             ),
        .disp_dst_i         ( disp_req.dst              ),
        .disp_src_required_i( disp_req.srcs_required    ),
        .disp_src_i         ( disp_req.srcs             ),

        // To Execution units
        .opc_valid_o       ( opc_valid          ),
        .eu_ready_i        ( eu_ready           ),
        .opc_tag_o         ( eu_req.tag         ),
        .opc_pc_o          ( eu_req.pc          ),
        .opc_act_mask_o    ( eu_req.active_mask ),
        .opc_inst_o        ( eu_req.inst        ),
        .opc_dst_o         ( eu_req.dst         ),
        .opc_operand_data_o( eu_req.src_data    ),

        // From Execution units
        .opc_to_eu_ready_o( opc_to_eu_ready ),
        .eu_valid_i       ( eu_valid        ),
        .eu_tag_i         ( eu_rsp.tag      ),
        .eu_dst_i         ( eu_rsp.dst      ),
        .eu_data_i        ( eu_rsp.data     )
    );

    // ########################################################################################
    // # Simulation Logic                                                                     #
    // ########################################################################################

    disp_req_t disp_requests[$];
    eu_req_t   eu_requests  [$];

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
            #AcqDelay;
            #1ns;

            if (opc_ready && disp_valid && initialized) begin
                // Add dispatch request to the queue
                disp_requests.push_back(disp_req);
                $display("Dispatch req: Tag %0h, PC %0h, Active Mask %b, Dst %0d, Inst %0h, Req %b",
                    disp_req.tag, disp_req.pc, disp_req.active_mask, disp_req.dst, disp_req.inst,
                    disp_req.srcs_required);
            end

            if (opc_valid && eu_ready) begin
                // Add to EU requests
                eu_requests.push_back(eu_req);
                $display("EU req: Tag %0h, PC %0h, Active Mask %b, Dst %0d, Inst %0h, Src Data %h",
                    eu_req.tag, eu_req.pc, eu_req.active_mask, eu_req.dst, eu_req.inst,
                    eu_req.src_data);
            end

            if (disp_requests.size() == 0 || eu_requests.size() == 0) begin
                continue;
            end

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
                        if (!disp.srcs_required[j]) begin
                            continue; // Skip if the source is not required
                        end

                        wid = 0;
                        reg_idx = 0;

                        if (NumWarps > 1)
                            wid[WidWidth-1:0] = eu.tag[WidWidth-1:0];

                        reg_idx[RegIdxWidth-1:0] = disp.srcs[j];

                        if (eu.src_data[j] != reg_file[wid][reg_idx]) begin
                            $display("Mismatch in source data for operand %0d", j);
                            $error("Expected: %0d, Got: %0d",
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
            else $error("No matching dispatch request found for Execution Unit request tag %0h!",
                eu.tag);
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

        disp_requests = {};
        eu_requests   = {};

        $timeformat(-9, 0, "ns", 12);
        // configure VCD dump
        $dumpfile("register_opc_stage.vcd");
        $dumpvars(1,i_register_opc_stage);

        $display("Initializing registers...");
        eu_valid = 1'b0;
        eu_rsp   = '{default: 0};
        @(posedge clk);
        @(posedge clk);
        while(!rst_n) begin
            @(posedge clk);
        end

        for (int wid = 0; wid < NumWarps; wid++) begin
            for (int reg_idx = 0; reg_idx < (1 << RegIdxWidth); reg_idx++) begin
                #ApplDelay;
                eu_valid = 1'b1;
                eu_rsp.tag[WidWidth-1:0] = wid[WidWidth-1:0];
                eu_rsp.dst               = reg_idx[RegIdxWidth-1:0];

                reg_file[wid][reg_idx]   = randomize_ram_data();
                eu_rsp.data              = reg_file[wid][reg_idx];
                @(posedge clk);
                while(!opc_to_eu_ready) begin
                    @(posedge clk);
                end
            end
        end
        #ApplDelay;
        eu_valid    = 1'b0;
        @(posedge clk);

        $display("Starting simulation!");

        while(cycles < MaxSimCycles && insts_sent_to_eu < InstsToComplete) begin
            // Wait for clock edge
            @(posedge clk);
            #ApplDelay;
            initialized = 1'b1;
            #(AcqDelay-ApplDelay);
            cycles++;

            // Instruction dispatch
            if (disp_valid && opc_ready) begin
                dispatched_insts++;
                $display("Cycle %0d: Dispatching instruction", cycles);
                $display("\tTag: %0h", disp_req.tag);
                $display("\tPC: %0h", disp_req.pc);
                $display("\tActive Mask: %b", disp_req.active_mask);
                $display("\tInstruction: %0h", disp_req.inst);
                $display("\tDst reg: %0d", disp_req.dst);
                for (int i = 0; i < OperandsPerInst; i++) begin
                    $display("\tSrc[%0d] req: %0b reg: %0d", i, disp_req.srcs_required[i],
                        disp_req.srcs[i]);
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
                    && i_register_opc_stage.opc_eu_valid[i]
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

            // To Execution units
            if (opc_valid && eu_ready) begin
                insts_sent_to_eu++;
                $display("Cycle %0d: Sending instruction to Execution Unit", cycles);
                $display("\tTag: %0h", eu_req.tag);
                $display("\tTag (wid): %0h", eu_req.tag[WidWidth-1:0]);
                $display("\tPC: %0h", eu_req.pc);
                $display("\tActive Mask: %b", eu_req.active_mask);
                $display("\tInstruction: %0h", eu_req.inst);
                $display("\tDst reg: %0d", eu_req.dst);
                for (int i = 0; i < OperandsPerInst; i++) begin
                    $display("\tSrc[%0d] data: %0d", i, eu_req.src_data[i]);
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
