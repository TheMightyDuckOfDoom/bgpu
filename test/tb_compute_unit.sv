// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Testbench for Compute Unit
module tb_compute_unit #(
    /// Number of inflight instructions per warp
    parameter int unsigned InflightInstrPerWarp = 4,
    /// Width of the Program Counter
    parameter int unsigned PcWidth = 16,
    /// Number of warps
    parameter int unsigned NumWarps = 4,
    /// Number of threads per warp
    parameter int unsigned WarpWidth = 2,
    /// Encoded instruction width
    parameter int unsigned EncInstWidth = 32,
    /// Wait buffer size per warp
    parameter int unsigned WaitBufferSizePerWarp = 2,

    parameter int unsigned OperandsPerInst = 2,
    parameter int unsigned RegIdxWidth     = 8,

    parameter int unsigned MemorySize = 32,

    parameter time         TclkPeriod   = 10ns,
    parameter int unsigned MaxSimCycles = 1000
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

    logic opc_ready, disp_valid;
    iid_t disp_tag;
    pc_t  disp_pc;
    act_mask_t disp_act_mask;
    reg_idx_t disp_dst;
    reg_idx_t [OperandsPerInst-1:0] disp_operands;

    logic eu_valid, eu_valid_q, eu_valid_q2;
    iid_t eu_tag, eu_tag_q, eu_tag_q2;

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
        .disp_pc_o(disp_pc),
        .disp_act_mask_o(disp_act_mask),
        .disp_dst_o(disp_dst),
        .disp_operands_o(disp_operands),

        .eu_valid_i(eu_valid_q),
        .eu_tag_i(eu_tag_q)
    );

    // OPC queue
    iid_t opc_tags [$];

    // Dispatch
    initial begin
        opc_ready = 1'b0;
        @(posedge clk);
        while(1) begin
            #TCLKHALF;
            opc_ready = $urandom() % 1 == 0;

            @(posedge clk);
            if(opc_ready && disp_valid) begin
                opc_tags.push_back(disp_tag);
                $display("Dispatched instruction for warp %2d tag %2d",
                    disp_tag[WidWidth+TagWidth-1:TagWidth], disp_tag[TagWidth-1:0]);
            end
        end
    end

    // Execution Units
    initial begin
        int i;
        eu_valid = 1'b0;
        eu_tag = '0;
        while(1) begin
            if(opc_tags.size() > 0) begin
                eu_valid = $urandom_range(0, 3) == 0;
            end else begin
                eu_valid = 1'b0;
            end
            if(eu_valid) begin
                // Choose a random tag from the queue
                i = $urandom_range(0, opc_tags.size()-1);
                for(int j = 0; j < i; j++) begin
                    // Pop the first element and push it to the back
                    opc_tags.push_back(opc_tags.pop_front());
                end
                eu_tag = opc_tags.pop_front();
            end
            if(eu_valid_q)
                $display("Executing instruction for warp %2d tag %2d",
                    eu_tag[WidWidth+TagWidth-1:TagWidth], eu_tag[TagWidth-1:0]);
            @(posedge clk);
        end
    end

    always_ff @(posedge clk) begin
        if(!rst_n) begin
            eu_valid_q  <= 1'b0;
            eu_valid_q2 <= 1'b0;
            eu_tag_q    <= '0;
            eu_tag_q2   <= '0;
        end else begin
            eu_valid_q  <= eu_valid;
            eu_valid_q2 <= eu_valid_q;
            eu_tag_q    <= eu_tag;
            eu_tag_q2   <= eu_tag_q;
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
            if(disp_valid && opc_ready) begin
                // Get the instruction ID from the hashmap
                insn_id_in_sim[PcWidth-1:0] = disp_pc;
                insn_id_in_sim[PcWidth + WarpWidth - 1:PcWidth] = disp_act_mask;
                insn_id_in_sim[PcWidth + WarpWidth + WidWidth - 1:PcWidth + WarpWidth] =
                    disp_tag[WidWidth + TagWidth - 1:TagWidth];
                insn_id_in_file = insn_id_in_file_map[insn_id_in_sim];

                opc_insn_id_in_file[disp_tag] = insn_id_in_file;

                // OPC Stage
                $fwrite(fd, "S\t%0d\t0\tOpC/Eu\n",
                    insn_id_in_file);
            end

            // Retire Stage
            if(eu_valid_q) begin
                insn_id_in_file = opc_insn_id_in_file[eu_tag_q];

                // Retire Stage
                $fwrite(fd, "S\t%0d\t0\tRet\n",
                    insn_id_in_file);
            end

            // Retire
            if(eu_valid_q2) begin
                insn_id_in_file = opc_insn_id_in_file[eu_tag_q2];

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
