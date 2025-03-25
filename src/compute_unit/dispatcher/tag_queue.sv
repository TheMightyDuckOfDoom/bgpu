// Copyright 2024 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Authors:
// - Thomas Benz  <tbenz@iis.ee.ethz.ch>
// - Tobias Senti <tsenti@ethz.ch>

`include "common_cells/assertions.svh"
`include "common_cells/registers.svh"

/// Based on common_cells/passthrough_stream_fifo.sv

/// Stream FIFO that does not cut the timing path. When full; pushing data is allowed if in
/// the same cycle data is popped. Creates longer timing paths but can use buffer space more
/// efficiently.
module tag_queue #(
    /// Depth can be arbitrary from 2 to 2**32
    parameter int unsigned Depth       = 32'd8,
    /// Print information when the simulation launches
    parameter bit          PrintInfo   = 1'b0,
    /// If the FIFO is full, allow reading and writing in the same cycle
    parameter bit          SameCycleRW = 1'b1,
    
    /// Dependent parameter, do **not** overwrite.
    parameter int          TagWidth    = $clog2(Depth),
    parameter type         type_t      = logic[TagWidth-1:0]
) (
    /// Clock
    input  logic                 clk_i,
    /// Asynchronous reset active low
    input  logic                 rst_ni,
    /// Fifo flush
    input  logic                 flush_i,
    /// data to push into the FIFO
    input  type_t                tag_i,
    /// input data valid
    input  logic                 valid_i,
    /// FIFO is not full
    output logic                 ready_o,
    /// output data
    output type_t                tag_o,
    /// FIFO is not empty
    output logic                 valid_o,
    /// pop head from FIFO
    input  logic                 ready_i
);
    /// Bit Width of the read and write pointers
    /// One additional bit to detect overflows
    localparam int unsigned PointerWidth = $clog2(Depth) + 1;

    // Read and write pointers
    logic [PointerWidth-1:0]  read_ptr_d,  read_ptr_q;
    logic [PointerWidth-1:0] write_ptr_d, write_ptr_q;

    // Data
    type_t [Depth-1 :0] data_d, data_q;

    // Enable storage
    logic load_data;

    assign tag_o = data_q[read_ptr_q[PointerWidth-2:0]];

    // Logic
    always_comb begin
        // Default
        load_data   = 1'b0;
        read_ptr_d  = read_ptr_q;
        write_ptr_d = write_ptr_q;
        data_d      = data_q;

        if (flush_i) begin // Flush
            read_ptr_d  = 'd1 << PointerWidth-1;
            write_ptr_d = '0;
            valid_o     = 1'b0;
            ready_o     = 1'b0;

            load_data   = 1'b1;
            for (int i = 0; i < Depth; i++) begin
                data_d[i] = i[TagWidth-1:0];
            end

        end else begin
            // Read
            valid_o = read_ptr_q[PointerWidth-1] == write_ptr_q[PointerWidth-1]
                ? read_ptr_q[PointerWidth-2:0] != write_ptr_q[PointerWidth-2:0] : 1'b1;
            if (ready_i) begin
                if (read_ptr_q[PointerWidth-2:0] == (Depth[PointerWidth-2:0]-'d1)) begin
                    // On overflow reset pointer to zero and flip imaginary bit
                    read_ptr_d[PointerWidth-2:0] = '0;
                    read_ptr_d[PointerWidth-1]   = !read_ptr_q[PointerWidth-1];
                end else begin
                    // Increment counter
                    read_ptr_d = read_ptr_q + 'd1;
                end
            end

            // Write -> Also able to write if we read in the same cycle
            ready_o     = (read_ptr_q[PointerWidth-1] == write_ptr_q[PointerWidth-1]
                ? 1'b1 : write_ptr_q[PointerWidth-2:0] != read_ptr_q[PointerWidth-2:0])
                || (SameCycleRW && ready_i && valid_o);

            if (valid_i) begin
                load_data = 1'b1;
                data_d[write_ptr_q[PointerWidth-2:0]] = tag_i;

                if (write_ptr_q[PointerWidth-2:0] == (Depth[PointerWidth-2:0]-'d1)) begin
                    // On overflow reset pointer to zero and flip imaginary bit
                    write_ptr_d[PointerWidth-2:0] = '0;
                    write_ptr_d[PointerWidth-1]   = !write_ptr_q[PointerWidth-1];
                end else begin
                    // Increment pointer
                    write_ptr_d = write_ptr_q + 'd1;
                end
            end
        end
    end

    // Flip Flops
    `FF( read_ptr_q,  read_ptr_d, 'd1 << PointerWidth-1, clk_i, rst_ni)
    `FF(write_ptr_q, write_ptr_d, '0, clk_i, rst_ni)

    for(genvar i = 0; i < Depth; i++) begin : gen_ff
        `FFL(data_q[i], data_d[i], load_data, i[TagWidth-1:0], clk_i, rst_ni)
    end : gen_ff
    //`FFL(data_q, data_d, load_data, '0, clk_i, rst_ni)

    // no full push
    `ASSERT_NEVER(CheckFullPush, (!ready_o & valid_i), clk_i, !rst_ni)
    // empty pop
    `ASSERT_NEVER(CheckEmptyPop, (!valid_o & ready_i), clk_i, !rst_ni)

    `ifndef SYNTHESIS
        // Tags in flight queue
        logic [Depth-1:0] inflight_queue;

        always @(posedge clk_i) begin
            if(!rst_ni || flush_i) begin
                inflight_queue <= '0;
            end else begin
                // Read from queue -> add to inflight queue
                if (valid_o && ready_i) begin
                    // Check that the tag is not already in the queue
                    if(inflight_queue[tag_o])
                        $error("Tag %d already in inflight queue", tag_o);

                    inflight_queue[tag_o] <= 1'b1;
                end

                // Write to queue -> remove from inflight queue
                if (valid_i && ready_o) begin
                    // Make sure that tag is in the queue
                    if(!inflight_queue[tag_i])
                        $error("Tag %d not in inflight queue", tag_i);
                    inflight_queue[tag_i] <= 1'b0;
                end
            end
        end
    `endif

endmodule
