// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Testbench for Wdata Assembler
module tb_wdata_assembler #(
    // Simulation parameters
    parameter int unsigned InputsToCheck = 10000,

    // Width of the registers
    parameter int unsigned RegWidth = 32,
    // Number of threads in a warp
    parameter int unsigned WarpWidth = 4,
    // Block size in bytes
    parameter int unsigned BlockIdxbits = 4
) ();
    // #######################################################################################
    // # Local Parameters                                                                    #
    // #######################################################################################

    localparam int unsigned WriteWidthBits = (RegWidth + 7) / 8 > 1 ? $clog2((RegWidth + 7) / 8)
                                                : 1;
    localparam int unsigned ReqWidth       = WriteWidthBits
                                                + WarpWidth * (1 + RegWidth + BlockIdxbits);

    // #######################################################################################
    // # Type Definitions                                                                    #
    // #######################################################################################

    typedef logic [           WarpWidth-1:0] act_mask_t;
    typedef logic [RegWidth * WarpWidth-1:0] warp_data_t;
    typedef logic [      WriteWidthBits-1:0] write_width_t;

    typedef logic [           BlockIdxbits-1:0] block_offset_t;
    typedef logic [    (1 << BlockIdxbits)-1:0] block_mask_t;
    typedef logic [(1 << BlockIdxbits) * 8-1:0] block_data_t;

    typedef struct packed {
        act_mask_t    we_mask;
        warp_data_t   wdata;
        write_width_t write_width;
        block_offset_t [WarpWidth-1:0] block_offsets;
    } req_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Inputs
    req_t req;

    // Outputs
    block_mask_t mem_we_mask;
    block_data_t mem_wdata;

    // #######################################################################################
    // # DUT Instantiation                                                                   #
    // #######################################################################################

    wdata_assembler #(
        .RegWidth    ( RegWidth     ),
        .WarpWidth   ( WarpWidth    ),
        .BlockIdxBits( BlockIdxbits )
    ) i_wdata_assembler (
        .we_mask_i      ( req.we_mask       ),
        .wdata_i        ( req.wdata         ),
        .write_width_i  ( req.write_width   ),
        .block_offsets_i( req.block_offsets ),

        .mem_we_mask_o( mem_we_mask ),
        .mem_wdata_o  ( mem_wdata   )
    );

    // #######################################################################################
    // # Testbench logic                                                                     #
    // #######################################################################################
    function static void randomize_req();
        int unsigned rand_data;
        if (ReqWidth <= 32) begin
        // If the data width is less than or equal to 32 bits, randomize the entire data_o.
        rand_data = $urandom;
        /* verilator lint_off SELRANGE */
        req = rand_data[ReqWidth - 1:0];
        /* verilator lint_on SELRANGE */
        end else begin
            /* verilator lint_off UNSIGNED */
            for (int i = 0; i <= (ReqWidth + ReqWidth / 2) / 32; i++) begin
            /* verilator lint_on UNSIGNED */
                rand_data = $urandom;
                /* verilator lint_off SELRANGE */
                req[i*32+:32] = rand_data;
                /* verilator lint_on SELRANGE */
            end
        end
        if (int'(req.write_width) > $clog2((RegWidth + 7) / 8)) begin
            rand_data = $clog2((RegWidth + 7) / 8);
            req.write_width = rand_data[WriteWidthBits-1:0];
        end
    endfunction

    initial begin
        block_mask_t expected_we_mask;
        block_data_t expected_wdata;

        logic [RegWidth-1:0] thread_truncated;
        block_mask_t thread_we_mask;

        for(int i = 0; i < InputsToCheck; i++) begin
            // Randomize the request
            randomize_req();

            // Check the output
            #1ns;

            $display("Input:");
            $display("  we_mask: %b", req.we_mask);
            $display("  write_width: %d", 1 << req.write_width);
            for(int thread = 0; thread < WarpWidth; thread++) begin
                $display("  thread %0d:", thread);
                $display("    wdata: %h", req.wdata[thread * RegWidth +: RegWidth]);
                $display("    block_offset: %d", req.block_offsets[thread]);
            end

            $display("Output:");
            $display("  mem_wdata: %h", mem_wdata);
            $display("  mem_we_mask: %b", mem_we_mask);

            expected_we_mask = '0;
            expected_wdata   = '0;
            for(int thread = 0; thread < WarpWidth; thread++) begin
                if(!req.we_mask[thread])
                    continue;

                // Truncate the write data to the correct width
                $display("  thread %0d: truncating write data", thread);
                thread_truncated = req.wdata[thread * RegWidth +: RegWidth];
                thread_truncated = thread_truncated & ((1 << (1 << req.write_width) * 8) - 1);
                $display("    thread_truncated: %h", thread_truncated);

                thread_we_mask = (1 << (1 << req.write_width)) - 1;
                thread_we_mask = thread_we_mask << req.block_offsets[thread];
                $display("    thread_we_mask: %b", thread_we_mask);

                // Or the write data into the expected output
                expected_wdata = expected_wdata |
                    /* verilator lint_off WIDTHEXPAND */
                    (thread_truncated << (req.block_offsets[thread] * 8));
                    /* verilator lint_on WIDTHEXPAND */

                expected_we_mask = expected_we_mask | thread_we_mask;
            end
            $display("  expected_wdata: %h", expected_wdata);
            $display("  expected_we_mask: %b", expected_we_mask);

            assert(mem_wdata == expected_wdata)
            else $error("Mismatch at input %0d: mem_wdata = %h, expected_wdata = %h", i, mem_wdata,
                expected_wdata);

            assert(mem_we_mask == expected_we_mask)
            else $error("Mismatch at input %0d: mem_we_mask = %b, expected_we_mask = %b", i,
                mem_we_mask, expected_we_mask);
        end

        $finish();
    end

endmodule : tb_wdata_assembler
