// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "common_cells/registers.svh"

/// Register Table
// Maps a register to a tag that produces the most recent value
module reg_table #(
    parameter int unsigned NumTags         = 8,
    parameter int unsigned RegIdxWidth     = 6,
    parameter int unsigned OperandsPerInst = 2,

    parameter int unsigned TagWidth  = $clog2(NumTags),
    parameter type         tag_t     = logic [   TagWidth-1:0],
    parameter type         reg_idx_t = logic [RegIdxWidth-1:0]
) (
    input logic clk_i,
    input logic rst_ni,

    // From Decoder
    output logic space_available_o,
    input logic insert_i,
    input tag_t tag_i,
    input reg_idx_t dst_reg_i,
    input reg_idx_t [OperandsPerInst-1:0] operands_reg_i,

    // To Wait Buffer
    output logic [OperandsPerInst-1:0] operands_ready_o,
    output tag_t [OperandsPerInst-1:0] operands_tag_o,

    // From Execution Unit
    input  logic eu_valid_i,
    input  tag_t eu_tag_i
);

    // ######################################################################
    // # Typedefs                                                          #
    // ######################################################################

    // Regsiter Table Entry
    typedef struct packed {
        reg_idx_t dst;
        tag_t     producer;
    } reg_table_entry_t;

    // ######################################################################
    // # Signals                                                           #
    // ######################################################################

    logic [NumTags-1:0] table_valid_q, table_valid_d;
    reg_table_entry_t [NumTags-1:0] table_q, table_d;

    logic use_existing_entry;

    // ######################################################################
    // # Combinational Logic                                               #
    // ######################################################################

    // Space available if not all entries are valid
    // |-> in theory we could even accept a new one if an existing dst is overwritten/updated
    assign space_available_o = !(&table_valid_q);

    // Insert logic
    always_comb begin
        // Default
        table_valid_d = table_valid_q;
        table_d       = table_q;

        operands_ready_o = '0;
        operands_tag_o   = '0;

        use_existing_entry = 1'b0;

        // Insert logic
        if(insert_i && space_available_o) begin : insert_logic
            // First check operands
            for(int op = 0; op < OperandsPerInst; op++) begin : check_operand
                operands_ready_o[op] = 1'b1;
                // Check all entries, if valid and the destination is the same as the operand |-> not ready
                for(int entry = 0; entry < NumTags; entry++) begin : check_entry
                    if(table_valid_q[entry] && table_q[entry].dst == operands_reg_i[op]) begin
                        operands_ready_o[op] = 1'b0;
                        operands_tag_o[op]   = table_q[entry].producer;
                        break;
                    end
                end : check_entry

                // Check if operand is produced by the EUs in the same cycle |-> then it is ready
                if(eu_valid_i && eu_tag_i == operands_tag_o[op]) begin
                    operands_ready_o[op] = 1'b1;
                end
            end : check_operand

            // Insert destination, first check if dst is already in table
            for(int entry = 0; entry < NumTags; entry++) begin : check_existing_entries
                if(table_valid_q[entry] && table_q[entry].dst == dst_reg_i) begin
                    table_valid_d[entry]    = 1'b1;
                    table_d[entry].producer = tag_i;
                    use_existing_entry      = 1'b1;
                    break;
                end
            end : check_existing_entries

            // If not, find a free entry
            if(!use_existing_entry) begin : use_free_entry
                for(int entry = 0; entry < NumTags; entry++) begin : find_free_entry
                    if(!table_valid_q[entry]) begin
                        table_valid_d[entry]    = 1'b1;
                        table_d[entry].dst      = dst_reg_i;
                        table_d[entry].producer = tag_i;
                        break;
                    end
                end : find_free_entry
            end : use_free_entry
        end : insert_logic

        // Clear logic
        // |-> if the EU is valid, clear all entries with the same producer tag, as result is in register file
        if(eu_valid_i) begin : clear_entry
            for(int entry = 0; entry < NumTags; entry++) begin
                if(table_valid_q[entry] && table_q[entry].producer == eu_tag_i) begin
                    table_valid_d[entry] = 1'b0;
                end
            end
        end : clear_entry
    end

    // ######################################################################
    // # Sequential Logic                                                   #
    // ######################################################################

    for(genvar i = 0; i < NumTags; i++) begin : gen_ffs
        `FF(table_valid_q[i], table_valid_d[i], '0, clk_i, rst_ni);
        `FF(table_q[i], table_d[i], '0, clk_i, rst_ni);
    end

    // ######################################################################
    // # Assertions                                                        #
    // ######################################################################

    `ifndef SYNTHESIS
        // Check that there is space available when inserting
        assert property (@(posedge clk_i) insert_i |-> space_available_o)
        else $error("No space available in register table when inserting");

        // Check that there a no entries with matching destination register or tag
        for(genvar i = 0; i < NumTags; i++) begin : gen_check_entries
            for(genvar j = 0; j < NumTags; j++) begin : gen_check_entries_inner
                // Check destination register
                assert property (@(posedge clk_i) disable iff(!rst_ni) table_valid_q[i]
                    && table_valid_q[j] |-> i == j || table_q[i].dst != table_q[j].dst)
                else $error("Destination register %d is in multiple entries: %d and %d",
                    table_q[i].dst, i, j);

                // Check producer tag
                assert property (@(posedge clk_i) disable iff(!rst_ni) table_valid_q[i]
                    && table_valid_q[j] |-> i == j || table_q[i].producer != table_q[j].producer)
                else $error("Producer tag %d is in multiple entries: %d and %d",
                    table_q[i].producer, i, j);
            end : gen_check_entries_inner
        end : gen_check_entries
    `endif

endmodule : reg_table
