// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "bgpu/instructions.svh"

/// Testbench for Compute Unit
module tb_compute_unit #(
    /// Width of the Program Counter
    parameter int unsigned PcWidth = 16,
    /// Number of warps
    parameter int unsigned NumWarps = 4,
    /// Number of threads per warp
    parameter int unsigned WarpWidth = 4,
    /// Wait buffer size per warp
    parameter int unsigned WaitBufferSizePerWarp = 1,
    /// Number of inflight instructions per warp
    parameter int unsigned InflightInstrPerWarp = WaitBufferSizePerWarp * 2,

    parameter int unsigned NumBanks = 4,
    parameter int unsigned NumOperandCollectors = 6,
    parameter int unsigned OperandsPerInst = 2,
    parameter int unsigned RegIdxWidth     = 8,
    parameter int unsigned RegWidth       = 16,

    parameter time         TclkPeriod   = 10ns,
    parameter int unsigned MaxSimCycles = 1000
);
    localparam time TCLKHALF = TclkPeriod / 2;
    localparam int WidWidth = NumWarps > 1 ? $clog2(NumWarps) : 1;
    localparam int TagWidth = $clog2(InflightInstrPerWarp);

    typedef logic [     PcWidth-1:0] pc_t;
    typedef logic [   WarpWidth-1:0] act_mask_t;
    typedef logic [ RegIdxWidth-1:0] reg_idx_t;
    typedef logic [WidWidth+TagWidth-1:0] iid_t;

    typedef struct packed {
        bgpu_eu_e eu;
        bgpu_inst_subtype_u subtype;
        reg_idx_t dst;
        reg_idx_t op1;
        reg_idx_t op2;
    } enc_inst_t;

    enc_inst_t test_program [8] = {
        '{eu: BGPU_INST_TYPE_IU, subtype: IU_TID, dst: 0, op1: 0, op2: 0},
        '{eu: BGPU_INST_TYPE_IU, subtype: IU_LDI, dst: 1, op1: 1, op2: 1},
        '{eu: BGPU_INST_TYPE_IU, subtype: IU_LDI, dst: 2, op1: 2, op2: 2},
        '{eu: BGPU_INST_TYPE_IU, subtype: IU_ADD, dst: 3, op1: 1, op2: 2},
        '{eu: BGPU_INST_TYPE_IU, subtype: IU_SUB, dst: 4, op1: 3, op2: 2},
        '{eu: BGPU_INST_TYPE_IU, subtype: IU_ADD, dst: 0, op1: 0, op2: 0},
        '{eu: BGPU_INST_TYPE_IU, subtype: IU_ADD, dst: 0, op1: 0, op2: 0},
        '{eu: BGPU_INST_TYPE_IU, subtype: IU_ADD, dst: 0, op1: 0, op2: 0}
    };

    logic initialized, stop;
    logic clk, rst_n, set_ready_status;

    // Generate clock
    initial clk = 1'b1;
    always begin
        #TCLKHALF clk = ~clk;
    end

    // Reset
    initial begin
        set_ready_status = 1'b0;
        rst_n = 1;
        @(posedge clk);

        wait(initialized);
        $display("Starting reset...");

        rst_n = 0;
        repeat(2) @(posedge clk);
        rst_n = 1;
        $display("Reset released.");
        set_ready_status = 1'b1;
        @(posedge clk);
        set_ready_status = 1'b0;
    end

    logic [NumWarps-1:0] warp_active, warp_stopped;

    logic ic_write;
    pc_t ic_write_pc;
    enc_inst_t ic_write_inst;

    // Instantiate Compute Unit
    /* verilator lint_off PINMISSING */
    compute_unit #(
        .NumTags(InflightInstrPerWarp),
        .PcWidth(PcWidth),
        .NumWarps(NumWarps),
        .WarpWidth(WarpWidth),
        .EncInstWidth($bits(enc_inst_t)),
        .WaitBufferSizePerWarp(WaitBufferSizePerWarp),
        .RegIdxWidth(RegIdxWidth),
        .OperandsPerInst(OperandsPerInst),
        .NumBanks(NumBanks),
        .NumOperandCollectors(NumOperandCollectors),
        .RegWidth(RegWidth)
    ) i_cu (
        .clk_i(clk),
        .rst_ni(rst_n),
        .set_ready_i(set_ready_status),
        .warp_active_o(warp_active),
        .warp_stopped_o(warp_stopped),
        .ic_write_i(ic_write),
        .ic_write_pc_i(ic_write_pc),
        .ic_write_inst_i(ic_write_inst)
    );
    /* verilator lint_on PINMISSING */

    // Initialize memory
    initial begin
        int unsigned program_size;
        initialized = 1'b0;
        stop = 1'b0;

        $timeformat(-9, 0, "ns", 12);
        // configure VCD dump
        $dumpfile("cu.vcd");
        $dumpvars(1,i_cu);

        $display("Initializing memory...");

        @(posedge clk);

        ic_write = 1'b1;
        program_size = $bits(test_program) / $bits(enc_inst_t);
        for(int i = 0; i < program_size; i++) begin
            ic_write_pc = i[PcWidth-1:0];
            ic_write_inst = test_program[i];
            @(posedge clk);
        end
        ic_write_pc   = program_size[PcWidth-1:0];
        ic_write_inst = '1;
        @(posedge clk);

        ic_write = 1'b0;

        initialized = 1'b1;
        $display("Memory initialized.");
    end

    // Monitor output
    int cycles;
    initial begin
        cycles = 0;
        wait(initialized);

        while(1) begin
            @(posedge clk);
            $display("Cycle %4d Time %8d", cycles, $time);
            if(rst_n) begin
                // Output from fetcher
                $display("Fetcher output valid: %b", i_cu.fe_to_ic_valid_d);
                if(i_cu.fe_to_ic_valid_d) begin
                    $display("Instruction at PC %d", i_cu.fe_to_ic_data_d.pc);
                    $display("Act. mask:        %b", i_cu.fe_to_ic_data_d.act_mask);
                    $display("Warp ID:          %d", i_cu.fe_to_ic_data_d.warp_id);
                end else begin
                    $display("Instruction at PC X");
                    $display("Act. mask:        X");
                    $display("Warp ID:          X");
                end

                $display("Decoder output valid: %b", i_cu.dec_to_ib_valid_q);
                if(i_cu.dec_to_ib_valid_q) begin
                    $display("Instruction at PC %d", i_cu.dec_to_ib_data_q.pc);
                    $display("Act. mask:        %b", i_cu.dec_to_ib_data_q.act_mask);
                    $display("Warp ID:          %d", i_cu.dec_to_ib_data_q.warp_id);
                end else begin
                    $display("Instruction at PC X");
                    $display("Act. mask:        X");
                    $display("Warp ID:          X");
                end

                // Check if there are still active warps
                if(warp_active == '0) begin
                    $display("\nAll warps are no longer active.");
                end

                if(warp_stopped == '1) begin
                    $display("\nAll warps have stopped.");
                    assert((warp_stopped & warp_active) == '0)
                    else $error("Warps %b have stopped, but %b are still active.",
                        warp_stopped, warp_active);
                    stop = 1'b1;
                end
            end

            cycles++;

            $display("\n");
        end
    end

    for(genvar warp = 0; warp < NumWarps; warp++) begin : gen_display_dispatcher
        initial begin
            wait(initialized);
            while(1) begin
                @(posedge clk);
                $display("Warp %2d", warp);
                $display("Register Table");
                $display("Entry   Vld Dst Prod");
                for(int rtentry = 0; rtentry < InflightInstrPerWarp; rtentry++) begin : gen_disp_rt
                    $display("RT[%2d]: %1d  %2d  %2d",
                        rtentry,
                        i_cu.i_warp_dispatcher.gen_dispatcher[warp]
                            .i_dispatcher.i_reg_table.table_valid_q[rtentry],
                        i_cu.i_warp_dispatcher.gen_dispatcher[warp]
                            .i_dispatcher.i_reg_table.table_q[rtentry].dst,
                        i_cu.i_warp_dispatcher.gen_dispatcher[warp]
                            .i_dispatcher.i_reg_table.table_q[rtentry].producer
                    );
                end : gen_disp_rt
                $display();

                $display("Wait buffer");
                $write("Entry   Vld Rdy PC  Tag Dst");
                for(int operand = 0; operand < OperandsPerInst; operand++) begin
                    $write("  Rdy Tag Op%1d", operand);
                end
                $display();
                for(int wbentry = 0; wbentry < WaitBufferSizePerWarp; wbentry++) begin
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
                    for(int operand = 0; operand < OperandsPerInst; operand++) begin
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

        wait(initialized);
        while(!stop) begin
            @(posedge clk);
            // Cycle
            $fwrite(fd, "C\t1\n");

            // Fetcher
            if(i_cu.fe_to_ic_valid_d && i_cu.ic_to_fe_ready_q) begin
                insn_id_in_sim[PcWidth-1:0] = i_cu.fe_to_ic_data_d.pc;
                insn_id_in_sim[PcWidth + WarpWidth - 1:PcWidth] = i_cu.fe_to_ic_data_d.act_mask;
                insn_id_in_sim[PcWidth + WarpWidth + WidWidth - 1:PcWidth + WarpWidth] =
                    i_cu.fe_to_ic_data_d.warp_id;

                // Add to hashmap
                assert(insn_id_in_file_map[insn_id_in_sim] == 0)
                else $error("Instruction %0d already exists in file.", insn_id_in_sim);

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
            if(i_cu.fe_to_ic_valid_q && i_cu.ic_to_fe_ready_d) begin
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
            if(i_cu.ic_to_dec_valid_q && i_cu.dec_to_ic_ready_d) begin
                // Get the instruction ID from the hashmap
                insn_id_in_sim[PcWidth-1:0] = i_cu.ic_to_dec_data_q.pc;
                insn_id_in_sim[PcWidth + WarpWidth - 1:PcWidth] = i_cu.ic_to_dec_data_q.act_mask;
                insn_id_in_sim[PcWidth + WarpWidth + WidWidth - 1:PcWidth + WarpWidth] =
                    i_cu.ic_to_dec_data_q.warp_id;
                insn_id_in_file = insn_id_in_file_map[insn_id_in_sim];

                // Decoder Stage
                $fwrite(fd, "S\t%0d\t0\tD\n",
                    insn_id_in_file);
            end

            // Start Dispatcher Stage
            if(i_cu.dec_to_ib_valid_q && i_cu.ib_to_dec_ready_d) begin
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
            if(i_cu.disp_to_opc_valid && i_cu.opc_to_disp_ready) begin
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
            if (i_cu.opc_to_eu_valid && i_cu.eu_to_opc_ready) begin
                // Get the instruction ID from the hashmap

                insn_id_in_file = opc_insn_id_in_file[i_cu.opc_to_eu_data.tag];

                // Execute Stage
                $fwrite(fd, "S\t%0d\t0\tEu\n",
                    insn_id_in_file);
            end

            // Retire
            if(i_cu.eu_to_opc_valid && i_cu.opc_to_eu_ready) begin
                insn_id_in_file = opc_insn_id_in_file[i_cu.eu_to_opc_data.tag];

                // Retire
                $fwrite(fd, "R\t%0d\t%0d\t0\n",
                    insn_id_in_file, retire_id);
                retire_id++;
            end
        end

        // Close file
        $fclose(fd);
    end : kanata_format

    // Max simulation cycles
    logic error;
    initial begin
        error = 1'b0;
        repeat(MaxSimCycles) @(posedge clk);
        $display("Max simulation cycles reached.");
        stop = 1'b1;
    end

    // Stop simulation
    initial begin
        wait(stop);
        $display("Stopping simulation...");
        $dumpflush;
        if (error)
            $fatal(1);
        else
            $finish;
    end

endmodule : tb_compute_unit
