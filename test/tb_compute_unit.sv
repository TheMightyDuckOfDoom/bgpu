// Copyright March 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Testbench for Compute Unit
module tb_compute_unit #(
    /// Number of inflight instructions per warp
    parameter int InflightInstrPerWarp = 4,
    /// Width of the Program Counter
    parameter int PcWidth = 16,
    /// Number of warps
    parameter int NumWarps = 4,
    /// Number of threads per warp
    parameter int WarpWidth = 2,
    /// Encoded instruction width
    parameter int EncInstWidth = 32,
    /// Wait buffer size per warp
    parameter int WaitBufferSizePerWarp = 2,

    parameter int OperandsPerInst = 2,
    parameter int RegIdxWidth = 8,

    parameter int MemorySize = 32,

    parameter time TclkPeriod = 10ns,
    parameter int MaxSimCycles = 1000
);
    localparam time TCLKHALF = TclkPeriod / 2;
    localparam int WidWidth = $clog2(NumWarps);
    localparam int TagWidth = $clog2(InflightInstrPerWarp);

    typedef logic [     PcWidth-1:0] pc_t;
    typedef logic [   WarpWidth-1:0] act_mask_t;
    typedef logic [EncInstWidth-1:0] enc_inst_t;
    typedef logic [ RegIdxWidth-1:0] reg_idx_t;
    typedef logic [WidWidth+TagWidth-1:0] iid_t;

    logic initialized, stop;
    logic clk, rst_n, set_ready_status;

    // Generate clock
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

    logic opc_ready, disp_valid;
    iid_t disp_tag;
    reg_idx_t disp_dst;
    reg_idx_t [OperandsPerInst-1:0] disp_operands;

    logic eu_valid;
    iid_t eu_tag;

    // Instantiate Compute Unit
    compute_unit #(
        .NumTags(InflightInstrPerWarp),
        .PcWidth(PcWidth),
        .NumWarps(NumWarps),
        .WarpWidth(WarpWidth),
        .EncInstWidth(EncInstWidth),
        .WaitBufferSizePerWarp(WaitBufferSizePerWarp),
        .RegIdxWidth(RegIdxWidth)
    ) i_cu (
        .clk_i(clk),
        .rst_ni(rst_n),
        .set_ready_i(set_ready_status),
        .warp_active_o(warp_active),
        .warp_stopped_o(warp_stopped),
        .ic_write_i(ic_write),
        .ic_write_pc_i(ic_write_pc),
        .ic_write_inst_i(ic_write_inst),

        .opc_ready_i(opc_ready),
        .disp_valid_o(disp_valid),
        .disp_tag_o(disp_tag),
        .disp_dst_o(disp_dst),
        .disp_operands_o(disp_operands),

        .eu_valid_i(eu_valid),
        .eu_tag_i(eu_tag)
    );

    // OPC queue
    iid_t opc_tags [$];

    // Dispatch
    initial begin
        opc_ready = 1'b0;
        while(1) begin
            opc_ready = $urandom() % 2 == 0;

            @(posedge clk);
            if(opc_ready && disp_valid) begin
                opc_tags.push_back(disp_tag);
                $display("Dispatched instruction with tag %d", disp_tag);
            end
        end
    end

    // Execution Units
    initial begin
        eu_valid = 1'b0;
        eu_tag = '0;
        while(1) begin
            if(opc_tags.size() > 0) begin
                eu_valid = $urandom() % 2 == 0;
            end else begin
                eu_valid = 1'b0;
            end
            if(eu_valid) begin
                eu_tag = opc_tags.pop_front();
                $display("Executing instruction with tag %d", eu_tag);
            end
            @(posedge clk);
        end
    end

    // Initialize memory
    initial begin
        initialized = 1'b0;
        stop = 1'b0;

        $timeformat(-9, 0, "ns", 12);
        // configure VCD dump
        $dumpfile("cu.vcd");
        $dumpvars(1,i_cu);

        $display("Initializing memory...");

        @(posedge clk);

        ic_write = 1'b1;
        for(int i = 0; i < MemorySize; i++) begin
            ic_write_pc = i[PcWidth-1:0];
            ic_write_inst = {i[7:0]+8'd1, i[7:0], i[7:0]-8'd1, i == MemorySize-1 ? 8'hFF : 8'd0};
            @(posedge clk);
        end
        ic_write = 1'b0;

        initialized = 1'b1;
        $display("Memory initialized.");
    end

    // Monitor output
    int cycles;
    initial cycles = 0;
    always @(posedge clk) begin
        $display("Cycle %d", cycles);
        if(rst_n) begin
            // Output from fetcher
            // $display("Fetcher output valid: %b", i_cu.fe_to_ic_valid_d);
            // if(i_cu.fe_to_ic_valid_d) begin
            //     $display("Instruction at PC %d", i_cu.fe_to_ic_data_d.pc);
            //     $display("Act. mask:        %b", i_cu.fe_to_ic_data_d.act_mask);
            //     $display("Warp ID:          %d", i_cu.fe_to_ic_data_d.warp_id);
            // end else begin
            //     $display("Instruction at PC X");
            //     $display("Act. mask:        X");
            //     $display("Warp ID:          X");
            // end

            // $display("Dispatch output valid: %b", disp_valid);
            // if(disp_valid) begin
            //     $display("Tag:              %d", disp_tag);
            //     $display("Destination:      %d", disp_dst);
            //     $display("Operands:         %3d %3d", disp_operands[0], disp_operands[1]);
            // end else begin
            //     $display("Tag:              X");
            //     $display("Destination:      X");
            //     $display("Operands:         XXX XXX");
            // end

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

    // Max simulation cycles
    initial begin
        repeat(MaxSimCycles) @(posedge clk);
        $display("Max simulation cycles reached.");
        $error;
    end

    // Stop simulation
    initial begin
        wait(stop);
        $display("Stopping simulation...");
        $dumpflush;
        $finish;
    end

endmodule : tb_compute_unit
