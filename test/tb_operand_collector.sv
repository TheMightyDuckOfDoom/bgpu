// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Testbench for Operand Collector
module tb_operand_collector import bgpu_pkg::*; #(
    // Simulation parameters
    parameter int unsigned MaxSimCycles     = 1000000,
    parameter int unsigned InstsToComplete  = 1000,
    parameter int unsigned WatchdogTimeout  = 1000,
    parameter int unsigned MaxMstWaitCycles = 100,

    // Simulation time parameters
    parameter time ClkPeriod = 10ns,
    parameter time ApplDelay = 1ns,
    parameter time AcqDelay  = 9ns,

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
    parameter int unsigned OperandsPerInst = 3,
    /// Width of a singled register
    parameter int unsigned RegWidth = OperandsPerInst * RegIdxWidth
) ();

    // ########################################################################################
    // # Local Parameters                                                                     #
    // ########################################################################################

    localparam int unsigned TagWidth = $clog2(NumTags);
    localparam int unsigned WidWidth = NumWarps > 1 ? $clog2(NumWarps) : 1;

    // ########################################################################################
    // # Type Definitions                                                                     #
    // ########################################################################################

    typedef logic [   TagWidth+WidWidth-1:0] iid_t;
    typedef logic [RegWidth * WarpWidth-1:0] data_t;
    typedef logic [             PcWidth-1:0] pc_t;
    typedef logic [           WarpWidth-1:0] act_mask_t;
    typedef logic [         RegIdxWidth-1:0] reg_idx_t;
    typedef logic [            WidWidth-1:0] wid_t;

    typedef struct packed {
        iid_t      tag;
        pc_t       pc;
        act_mask_t act_mask;
        inst_t     inst;
        reg_idx_t  dst;
        logic      [OperandsPerInst-1:0] src_is_reg;
        reg_idx_t  [OperandsPerInst-1:0] src;
        data_t     [OperandsPerInst-1:0] data;
    } insert_inst_t;

    typedef struct packed {
        wid_t     wid;
        reg_idx_t reg_idx;
    } read_req_t;

    typedef struct packed {
        wid_t  wid;
        data_t data;
    } read_rsp_t;

    typedef struct packed {
        iid_t      tag;
        pc_t       pc;
        act_mask_t act_mask;
        inst_t     inst;
        reg_idx_t  dst;
        data_t     [OperandsPerInst-1:0] data;
    } eu_inst_t;

    // ########################################################################################
    // # Signals                                                                              #
    // ########################################################################################

    logic         insert_inst_valid, insert_inst_ready;
    insert_inst_t insert_inst_req;

    insert_inst_t inserted_inst_q;

    logic      [OperandsPerInst-1:0] read_req_valid, read_req_valid_q, read_req_ready;
    reg_idx_t  [OperandsPerInst-1:0] read_req_reg_idx;
    wid_t      [OperandsPerInst-1:0] read_req_wid;
    read_req_t [OperandsPerInst-1:0] read_req;

    logic  [OperandsPerInst-1:0] read_rsp_valid, read_rsp_rand_valid;
    wid_t  [OperandsPerInst-1:0] read_rsp_wid;
    data_t [OperandsPerInst-1:0] read_rsp_data;

    logic opc_valid, eu_ready;
    eu_inst_t opc_inst;

    logic clk, rst_n;

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
    // # Stream Masters and Subordinates                                                     #
    // #######################################################################################

    // Instruction Insert Master -> Simulates Dispatcher
    rand_stream_mst #(
        .data_t       ( insert_inst_t    ),
        .ApplDelay    ( ApplDelay        ),
        .AcqDelay     ( AcqDelay         ),
        .MinWaitCycles( 0                ),
        .MaxWaitCycles( MaxMstWaitCycles )
    ) i_insert_inst_mst (
        .clk_i  ( clk               ),
        .rst_ni ( rst_n             ),
        .valid_o( insert_inst_valid ),
        .data_o ( insert_inst_req   ),
        .ready_i( insert_inst_ready )
    );

    // Register File Subordinates -> Simulates Register File
    for (genvar i = 0; i < OperandsPerInst; i++) begin : gen_operand_sub
        assign read_req[i].wid       = read_req_wid[i];
        assign read_req[i].reg_idx   = read_req_reg_idx[i];

        rand_stream_slv #(
            .data_t       ( read_req_t       ),
            .ApplDelay    ( ApplDelay        ),
            .AcqDelay     ( AcqDelay         ),
            .MinWaitCycles( 1                ),
            .MaxWaitCycles( MaxMstWaitCycles ),
            .Enqueue      ( 1'b1             )
        ) i_reg_file_sub (
            .clk_i  ( clk               ),
            .rst_ni ( rst_n             ),
            .data_i ( read_req[i]       ),
            .valid_i( read_req_valid[i] ),
            .ready_o( read_req_ready[i] )
        );

        always_ff @(posedge clk) begin
            if (read_rsp_valid[i])
                read_req_valid_q[i] <= 1'b0;
            else if (read_req_valid[i] && read_req_ready[i])
                read_req_valid_q[i] <= 1'b1;
        end

        rand_synch_holdable_driver #(
            .ApplDelay    ( ApplDelay        ),
            .MinWaitCycles( 1                ),
            .MaxWaitCycles( MaxMstWaitCycles )
        ) i_reg_file_data_sub (
            .clk_i  ( clk                    ),
            .rst_ni ( rst_n                  ),
            .hold_i ( 1'b0                   ),
            .data_o ( read_rsp_rand_valid[i] )
        );

        assign read_rsp_valid[i] = read_rsp_rand_valid[i] && read_req_valid_q[i];
    end : gen_operand_sub

    // Execution Unit Subordinate -> Simulates the execution unit
    rand_stream_slv #(
        .data_t       ( logic            ),
        .ApplDelay    ( ApplDelay        ),
        .AcqDelay     ( AcqDelay         ),
        .MinWaitCycles( 1                ),
        .MaxWaitCycles( MaxMstWaitCycles ),
        .Enqueue      ( 1'b1             )
    ) i_exec_unit_sub (
        .clk_i  ( clk       ),
        .rst_ni ( rst_n     ),
        .data_i ( 'd0       ),
        .valid_i( opc_valid ),
        .ready_o( eu_ready  )
    );

    // ##########################################################################################
    // # DUT Instantiation                                                                      #
    // ##########################################################################################

    operand_collector #(
        .NumTags        ( NumTags         ),
        .PcWidth        ( PcWidth         ),
        .NumWarps       ( NumWarps        ),
        .WarpWidth      ( WarpWidth       ),
        .RegIdxWidth    ( RegIdxWidth     ),
        .OperandsPerInst( OperandsPerInst ),
        .RegWidth       ( RegWidth        )
    ) i_operand_collector (
        .clk_i ( clk   ),
        .rst_ni( rst_n ),

        // From Dispatcher
        .opc_ready_o        ( insert_inst_ready          ),
        .disp_valid_i       ( insert_inst_valid          ),
        .disp_tag_i         ( insert_inst_req.tag        ),
        .disp_pc_i          ( insert_inst_req.pc         ),
        .disp_act_mask_i    ( insert_inst_req.act_mask   ),
        .disp_inst_i        ( insert_inst_req.inst       ),
        .disp_dst_i         ( insert_inst_req.dst        ),
        .disp_src_is_reg_i  ( insert_inst_req.src_is_reg ),
        .disp_src_i         ( insert_inst_req.src        ),

        // To Register File
        .opc_read_req_valid_o  ( read_req_valid   ),
        .opc_read_req_wid_o    ( read_req_wid     ),
        .opc_read_req_reg_idx_o( read_req_reg_idx ),
        .opc_read_req_ready_i  ( read_req_ready   ),

        // From Register File
        .opc_read_rsp_valid_i( read_rsp_valid ),
        .opc_read_rsp_data_i ( read_rsp_data  ),

        // To Execution Units
        .eu_ready_i         ( eu_ready          ),
        .opc_valid_o        ( opc_valid         ),
        .opc_tag_o          ( opc_inst.tag      ),
        .opc_pc_o           ( opc_inst.pc       ),
        .opc_act_mask_o     ( opc_inst.act_mask ),
        .opc_inst_o         ( opc_inst.inst     ),
        .opc_dst_o          ( opc_inst.dst      ),
        .opc_operand_data_o ( opc_inst.data     )
    );

    // ########################################################################################
    // # Simulation Logic                                                                     #
    // ########################################################################################

    initial begin : simulation_logic
        int unsigned cycles, inserted_insts, completed_insts, num_read_reqs, num_expected_reqs;
        data_t expected_data;

        cycles            = 0;
        inserted_insts    = 0;
        completed_insts   = 0;
        num_read_reqs     = 0;
        num_expected_reqs = 0;

        $display("Simulation started, running for %0d cycles", MaxSimCycles);

        while (cycles < MaxSimCycles && completed_insts < InstsToComplete) begin
            @(posedge clk);
            #AcqDelay;
            cycles++;

            // Insert instruction handshake
            if (insert_inst_valid && insert_inst_ready) begin
                inserted_insts++;
                inserted_inst_q = insert_inst_req;
                $display("Inserted instruction:");
                $display("  Tag: %0h", inserted_inst_q.tag);
                $display("  PC: %0h", inserted_inst_q.pc);
                $display("  Activate Mask: %0h", inserted_inst_q.act_mask);
                $display("  Instruction: %0h", inserted_inst_q.inst);
                $display("  Destination Register: %0h", inserted_inst_q.dst);
                for (int i = 0; i < OperandsPerInst; i++) begin
                    $display("  Source Register %0d: req %0b reg %0h Data: %0h",
                             i, insert_inst_req.src_is_reg[i], inserted_inst_q.src[i],
                             inserted_inst_q.data[i]);
                end
            end

            // Read request handshake
            for (int i = 0; i < OperandsPerInst; i++) begin
                if (read_req_valid[i] && read_req_ready[i]) begin
                    num_read_reqs++;
                    read_rsp_wid[i] = read_req[i].wid;
                    read_rsp_data[i] = inserted_inst_q.data[i];
                    $display("Cycle %0d: Read request  for wid=%0h, reg_idx=%0h",
                             cycles, read_rsp_wid[i], read_req[i].reg_idx);

                    assert(inserted_inst_q.src_is_reg[i] == 1'b1)
                    else $error("Source register %0d not required for instruction with tag %0h",
                                i, inserted_inst_q.tag);

                    assert (read_req[i].reg_idx == inserted_inst_q.src[i])
                    else $error("Read request reg_idx mismatch: expected %0h, got %0h",
                                inserted_inst_q.src[i], read_req[i].reg_idx);
                end

                if (read_rsp_valid[i]) begin
                    $display("Cycle %0d: Read response for wid=%0h, reg_idx=%0h, data=%0h",
                             cycles, read_rsp_wid[i], read_req_reg_idx[i], read_rsp_data[i]);
                end
            end

            // Execution unit handshake
            if (opc_valid && eu_ready) begin
                completed_insts++;
                num_expected_reqs += $countbits(inserted_inst_q.src_is_reg, 1'b1);
                $display("Cycle %0d:", cycles);
                $display("  Completed inst with tag %0h, pc %0h, act_mask %0h, dst %0h inst %0h",
                         opc_inst.tag, opc_inst.pc, opc_inst.act_mask, opc_inst.dst, opc_inst.inst);
                assert (opc_inst.tag == inserted_inst_q.tag)
                else $error("Instruction tag mismatch: expected %0h, got %0h",
                            inserted_inst_q.tag, opc_inst.tag);
                assert (opc_inst.pc == inserted_inst_q.pc)
                else $error("Instruction PC mismatch: expected %0h, got %0h",
                            inserted_inst_q.pc, opc_inst.pc);
                assert (opc_inst.act_mask == inserted_inst_q.act_mask)
                else $error("Instruction activate mask mismatch: expected %0h, got %0h",
                            inserted_inst_q.act_mask, opc_inst.act_mask);
                assert (opc_inst.inst == inserted_inst_q.inst)
                else $error("Instruction opcode mismatch: expected %0h, got %0h",
                            inserted_inst_q.inst, opc_inst.inst);
                assert (opc_inst.dst == inserted_inst_q.dst)
                else $error("Instruction destination register mismatch: expected %0h, got %0h",
                            inserted_inst_q.dst, opc_inst.dst);
                for (int i = 0; i < OperandsPerInst; i++) begin
                    $display("  Operand %0d: Data %0h", i, opc_inst.data[i]);
                    expected_data = '0;
                    if (inserted_inst_q.src_is_reg[i]) begin
                        expected_data = inserted_inst_q.data[i];
                    end else begin
                        for (int j = 0; j < WarpWidth; j++) begin
                            expected_data[j*RegWidth + i * RegIdxWidth +: RegIdxWidth]
                                = inserted_inst_q.src[i];
                        end
                    end

                    assert (opc_inst.data[i] == expected_data)
                    else $error("Instruction operand %0d data mismatch: expected %0h, got %0h",
                                i, expected_data, opc_inst.data[i]);
                end
            end
        end

        assert (inserted_insts > 0)
        else $error("No instructions were inserted during the simulation!");

        assert (completed_insts > 0)
        else $error("No instructions were completed during the simulation!");

        assert (completed_insts >= inserted_insts - 1)
        else $error("Completed insts (%0d) is less than inserted instructions (%0d)",
                    completed_insts, inserted_insts);

        $display("Inserted  %0d instructions during the simulation", inserted_insts);
        $display("Completed %0d instructions during the simulation", completed_insts);

        assert (num_read_reqs > 0)
        else $error("No read requests were made during the simulation!");

        assert(num_read_reqs >= num_expected_reqs)
        else $error("Number of read requests (%0d) is less than expected (%d)",
                    num_read_reqs, num_expected_reqs);

        assert(cycles < MaxSimCycles)
        else $error("Simulation exceeded maximum cycles (%0d)!", MaxSimCycles);

        assert(completed_insts == InstsToComplete)
        else $error("Completed instructions (%0d) does not match expected (%0d)!",
                    completed_insts, InstsToComplete);

        $display("Simulation ended after %0d cycles", cycles);
        $finish;
    end : simulation_logic

endmodule : tb_operand_collector
