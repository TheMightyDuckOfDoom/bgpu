// Copyright March 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Testbench for Compute Unit
module tb_compute_unit #(
    /// Width of the Program Counter
    parameter int PcWidth = 16,
    /// Number of warps
    parameter int NumWarps = 8,
    /// Number of threads per warp
    parameter int WarpWidth = 4,
    /// Encoded instruction width
    parameter int EncInstWidth = 32,

    parameter int MemorySize = 32,

    parameter time TCLK_PERIOD = 10ns,
    parameter int MaxSimCycles = 10000
);
    localparam TCLK_HALF = TCLK_PERIOD / 2;

    typedef logic [     PcWidth-1:0] pc_t;
    typedef logic [   WarpWidth-1:0] act_mask_t;
    typedef logic [EncInstWidth-1:0] enc_inst_t;

    logic initialized, stop;
    logic clk, rst_n, set_ready_status;

    // Generate clock
    always begin
        #TCLK_HALF clk = ~clk;
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

    logic[NumWarps-1:0] ib_space_available, new_ib_space_available;

    always_comb begin
        new_ib_space_available = {ib_space_available[NumWarps-2:0], ib_space_available[NumWarps-1]};
        new_ib_space_available = {new_ib_space_available[NumWarps-2:0], new_ib_space_available[NumWarps-1]};
        new_ib_space_available = {new_ib_space_available[NumWarps-2:0], new_ib_space_available[NumWarps-1]};
    end

    always @(posedge clk) begin
        if(!rst_n) begin
            ib_space_available <= 'd1;
        end else if(dec_valid) begin
            ib_space_available <= new_ib_space_available;
        end
    end

    logic [NumWarps-1:0] warp_active, warp_stopped;

    logic ic_write;
    pc_t ic_write_pc;
    enc_inst_t ic_write_inst;

    logic dec_valid;
    pc_t dec_pc;
    act_mask_t dec_act_mask;
    logic [$clog2(NumWarps)-1:0] dec_warp_id;
    logic [31:0] dec_inst;

    // Instantiate Compute Unit
    compute_unit #(
        .PcWidth(PcWidth),
        .NumWarps(NumWarps),
        .WarpWidth(WarpWidth),
        .EncInstWidth(EncInstWidth)
    ) i_cu (
        .clk_i(clk),
        .rst_ni(rst_n),
        .set_ready_i(set_ready_status),
        .warp_active_o(warp_active),
        .warp_stopped_o(warp_stopped),
        .ic_write_i(ic_write),
        .ic_write_pc_i(ic_write_pc),
        .ic_write_inst_i(ic_write_inst),
        .ib_space_available_i(ib_space_available),
        .disp_ready_i(1'b1),
        .dec_valid_o(dec_valid),
        .dec_pc_o(dec_pc),
        .dec_act_mask_o(dec_act_mask),
        .dec_warp_id_o(dec_warp_id),
        .dec_inst_o(dec_inst)
    );

    // Initialize memory
    initial begin
        initialized = 1'b0;
        stop = 1'b0;

        $timeformat(-9, 0, "ns", 12); // 1: scale (ns=-9), 2: decimals, 3: suffix, 4: print-field width
        // configure VCD dump
        $dumpfile("cu.vcd");
        $dumpvars(1,i_cu);

        $display("Initializing memory...");

        ic_write = 1'b1;
        for(int i = 0; i < MemorySize; i++) begin
            ic_write_pc = i[PcWidth-1:0];
            ic_write_inst = i;
            if(i == MemorySize-1) begin
                ic_write_inst = '1;
            end
            @(posedge clk);
        end
        ic_write = 1'b0;

        initialized = 1'b1;
        $display("Memory initialized.");
    end

    // Monitor output
    integer cycles;
    initial cycles = 0;
    always @(posedge clk) begin
        $display("Cycle %d", cycles);
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

            // Output from decoder
            $display("\nDecoder output valid: %b", dec_valid);
            if(dec_valid) begin
                $display("Instruction at PC %d", dec_pc);
                $display("Act. mask:        %b", dec_act_mask);
                $display("Warp ID:          %d", dec_warp_id);
                $display("Instruction:      %d", dec_inst);
            end else begin
                $display("Instruction at PC X");
                $display("Act. mask:        X");
                $display("Warp ID:          X");
                $display("Instruction:      X");
            end

            // Check if there are still active warps
            if(warp_active == '0) begin
                $display("\nAll warps are no longer active.");
            end

            if(warp_stopped == '1) begin
                $display("\nAll warps have stopped.");
                assert((warp_stopped & warp_active) == '0)
                else $fatal("Warps %b have stopped, but %b are still active.", warp_stopped, warp_active);
                stop = 1'b1;
            end
        end

        cycles++;

        $display("\n");
    end

    // Max simulation cycles
    initial begin
        repeat(MaxSimCycles) @(posedge clk);
        $display("Max simulation cycles reached.");
        $fatal;
    end

    // Stop simulation
    initial begin
        wait(stop);
        $display("Stopping simulation...");
        $dumpflush;
        $finish;
    end

endmodule : tb_compute_unit
