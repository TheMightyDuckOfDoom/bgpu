// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "common_cells/registers.svh"

/// Assembles the write data sent to the memory interface.
module wdata_assembler #(
    // Width of the registers
    parameter int unsigned RegWidth = 32,
    // Number of threads in a warp
    parameter int unsigned WarpWidth = 4,
    // Memory Block size in bytes -> Memory request width
    parameter int unsigned BlockIdxBits = 4,

    /// Dependent parameter, do **not** overwrite.
    parameter int unsigned RegWidthInBytes = (RegWidth + 7) / 8,
    parameter int unsigned WriteWidthBits  = RegWidthInBytes > 1 ? $clog2(RegWidthInBytes) : 1,
    parameter int unsigned BlockWidth      = 1 << BlockIdxBits, // In bytes
    parameter type write_width_t = logic [WriteWidthBits-1:0],
    parameter type byte_t        = logic  [                     7:0],
    parameter type block_data_t  = byte_t [          BlockWidth-1:0],
    parameter type block_mask_t  = logic  [          BlockWidth-1:0],
    parameter type block_idx_t   = logic  [        BlockIdxBits-1:0],
    parameter type act_mask_t    = logic  [           WarpWidth-1:0],
    parameter type warp_data_t   = logic  [RegWidth * WarpWidth-1:0]
) (
    // From Coalesce Splitter
    input act_mask_t    we_mask_i,
    input warp_data_t   wdata_i,
    input write_width_t write_width_i,
    input block_idx_t   [WarpWidth-1:0] block_offsets_i,

    // To Memory Interface
    output block_mask_t mem_we_mask_o,
    output block_data_t mem_wdata_o
);
    typedef logic [RegWidth-1:0] thread_data_t;
    typedef logic [RegWidthInBytes-1:0] thread_we_mask_t;

    thread_data_t    [WarpWidth-1:0] thread_wdata_raw;
    thread_we_mask_t thread_we_mask_raw;

    block_data_t [WarpWidth-1:0] thread_wdata;
    block_mask_t [WarpWidth-1:0] thread_we_mask;

    // Thread write mask -> which bytes are active
    assign thread_we_mask_raw = ('d1 << ('d1 << write_width_i)) - 'd1;

    // Shift the data and write mask by the block offsets for each thread
    for(genvar thread = 0; thread < WarpWidth; thread++) begin : gen_thread

        // Mask of upper unused bits of each thread's write data
        always_comb begin : mask_thread_wdata
            thread_wdata_raw[thread] = wdata_i[thread * RegWidth +: RegWidth];

            for(int byte_idx = 0; byte_idx < RegWidthInBytes; byte_idx++) begin : byte_loop
                // Mask the upper bits of the write data
                if (byte_idx >= (1 << write_width_i)) begin
                    thread_wdata_raw[thread][byte_idx * 8 +: 8] = '0;
                end
            end : byte_loop
        end : mask_thread_wdata

        // Assemble the write data for each thread -> shift it to the correct position withi the block
        assign thread_wdata[thread] = we_mask_i[thread] ?
            /* verilator lint_off WIDTHEXPAND */
            thread_wdata_raw[thread] << (8 * block_offsets_i[thread])
            /* verilator lint_on WIDTHEXPAND */
            : '0;

        assign thread_we_mask[thread] = we_mask_i[thread] ?
            /* verilator lint_off WIDTHEXPAND */
            thread_we_mask_raw << block_offsets_i[thread]
            /* verilator lint_on WIDTHEXPAND */
            : '0;
    end : gen_thread

    // Assemble the write data -> OR all threads block data together
    always_comb begin : combine_output
        // Default to zero
        mem_we_mask_o = '0;
        mem_wdata_o   = '0;

        for(int thread = 0; thread < WarpWidth; thread++) begin : thread_loop
            mem_we_mask_o = mem_we_mask_o | thread_we_mask[thread];
            mem_wdata_o   = mem_wdata_o   | thread_wdata  [thread];
        end : thread_loop
    end : combine_output

endmodule : wdata_assembler
