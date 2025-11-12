// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "common_cells/registers.svh"

/// Register Table
// Maps a register to a tag that produces the most recent value
module reg_table #(
    parameter int unsigned WarpWidth       = 2,
    parameter int unsigned NumTags         = 4,
    parameter int unsigned RegIdxWidth     = 2,
    parameter int unsigned OperandsPerInst = 2,

    parameter int unsigned TagWidth       = $clog2(NumTags),
    parameter int unsigned SubwarpIdWidth = WarpWidth > 1 ? $clog2(WarpWidth) : 1,
    parameter type         tag_t          = logic [      TagWidth-1:0],
    parameter type         reg_idx_t      = logic [   RegIdxWidth-1:0],
    parameter type         subwarp_id_t   = logic [SubwarpIdWidth-1:0]
) (
    /// Clock and Reset
    input logic clk_i,
    input logic rst_ni,

    /// To Fetcher -> Are all registers written to register file?
    // -> no pending instruction
    output logic all_dst_written_o,

    /// From Decoder
    output logic        space_available_o,
    input  logic        insert_i,
    input  tag_t        tag_i,
    input  subwarp_id_t subwarp_id_i,
    input  reg_idx_t    dst_reg_i,
    input  reg_idx_t [OperandsPerInst-1:0] operands_reg_i,

    /// To Wait Buffer
    output logic [OperandsPerInst-1:0] operands_ready_o,
    output tag_t [OperandsPerInst-1:0] operands_tag_o,

    /// From Execution Unit
    input logic eu_valid_i,
    input tag_t eu_tag_i
);

    // #######################################################################################
    // # Typedefs                                                                            #
    // #######################################################################################

    // Regsiter Table Entry
    typedef struct packed {
        subwarp_id_t subwarp_id;
        reg_idx_t    dst;
        tag_t        producer;
    } reg_table_entry_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Register Table
    logic             [NumTags-1:0] table_valid_q, table_valid_d;
    reg_table_entry_t [NumTags-1:0] table_q, table_d;

    // Reuse existing entry when inserting
    logic reuse_existing_entry;

    // #######################################################################################
    // # Combinational Logic                                                                 #
    // #######################################################################################

    // Space available if not all entries are valid
    // In theory we could even accept a new one if an existing dst is overwritten/updated,
    // but this would create a dependency between space_available_o and insert_i
    assign space_available_o = !(&table_valid_q);

    // All destination registers written if no entry is valid
    assign all_dst_written_o = !(|table_valid_q);

    // Determine if operand is ready and its tag
    always_comb begin : operand_check_logic
        // Default
        operands_ready_o = '1;
        operands_tag_o   = '0;

        // Check each operand
        for (int op = 0; op < OperandsPerInst; op++) begin : check_operand
            // Check all entries, if valid and the destination is the same as the operand
            // and part of the same subwarp |-> not ready, return tag
            for (int entry = 0; entry < NumTags; entry++) begin : check_entry
                if (table_valid_q[entry] && table_q[entry].dst == operands_reg_i[op]
                    && table_q[entry].subwarp_id == subwarp_id_i) begin : entry_found
                    // Not ready, return tag
                    operands_ready_o[op] = 1'b0;
                    operands_tag_o  [op] = table_q[entry].producer;
                    break;
                end : entry_found
            end : check_entry

            // Check if operand is produced by the EUs in the same cycle |-> then it is ready
            if (eu_valid_i && eu_tag_i == operands_tag_o[op]) begin
                operands_ready_o[op] = 1'b1;
            end
        end : check_operand
    end : operand_check_logic

    // Register Table Logic
    always_comb begin : reg_table_logic
        // Default
        table_valid_d = table_valid_q;
        table_d       = table_q;

        reuse_existing_entry = 1'b0;

        // Clear logic
        // |-> if the EU is valid, clear all entries with the same producer tag, as result is in register file
        if (eu_valid_i) begin : clear_entry
            for (int entry = 0; entry < NumTags; entry++) begin
                if (table_valid_q[entry] && table_q[entry].producer == eu_tag_i) begin
                    table_valid_d[entry] = 1'b0;
                end
            end
        end : clear_entry

        // Insert logic
        if (insert_i && space_available_o) begin : insert_logic
            // Insert destination, first check if dst is already in table
            for (int entry = 0; entry < NumTags; entry++) begin : check_existing_entries
                if (table_valid_q[entry] && table_q[entry].dst == dst_reg_i
                    && table_q[entry].subwarp_id == subwarp_id_i) begin : modify_existing
                    // Mark as valid, as we could have deallocated it in this cycle
                    table_valid_d[entry]    = 1'b1;
                    // Update producer tag
                    table_d[entry].producer = tag_i;
                    // Indicate that we reused an existing entry
                    reuse_existing_entry      = 1'b1;
                    break;
                end : modify_existing
            end : check_existing_entries

            // If not reusing an existing entry, find a free entry
            if (!reuse_existing_entry) begin : use_free_entry
                for (int entry = 0; entry < NumTags; entry++) begin : find_free_entry
                    if (!table_valid_q[entry]) begin : free_entry_found
                        // Mark as valid
                        table_valid_d[entry] = 1'b1;

                        // Set the entry
                        table_d[entry].dst        = dst_reg_i;
                        table_d[entry].producer   = tag_i;
                        table_d[entry].subwarp_id = subwarp_id_i;
                        break;
                    end : free_entry_found
                end : find_free_entry
            end : use_free_entry
        end : insert_logic
    end : reg_table_logic

    // #######################################################################################
    // # Sequential Logic                                                                    #
    // #######################################################################################

    `FF(table_valid_q, table_valid_d, '0, clk_i, rst_ni)
    `FF(table_q,       table_d,       '0, clk_i, rst_ni)

    // #######################################################################################
    // # Assertions                                                                          #
    // #######################################################################################

    `ifndef SYNTHESIS
        /// Check space_available_o and all_dst_written_o
        // If space_available_o is high, then we must have at least one free entry
        assert property (@(posedge clk_i) disable iff(!rst_ni)
            !(space_available_o) || (table_valid_q != '1))
            else $error("space_available_o is high, but all entries are occupied");

        // If all_dst_written_o is high, then no entries must be valid
        assert property (@(posedge clk_i) disable iff(!rst_ni)
            !(all_dst_written_o) || (table_valid_q == '0))
            else $error("all_dst_written_o is high, but some entries are still occupied");

        /// Check EU responses
        // Check if eu tag is in the table
        logic [$clog2(NumTags)-1:0] eu_match_index;
        logic eu_tag_in_table;
        always_comb begin : check_eu_tag_in_table
            eu_match_index  = '0;
            eu_tag_in_table = 1'b0;
            for (int entry = 0; entry < NumTags; entry++) begin
                if (table_valid_q[entry] && table_q[entry].producer == eu_tag_i) begin
                    eu_tag_in_table = 1'b1;
                    eu_match_index  = entry[$clog2(NumTags)-1:0];
                end
            end
        end : check_eu_tag_in_table

        // If EU valid and is in the table, then it mus be freed if it is not reused
        assert property (@(posedge clk_i) disable iff(!rst_ni)
            !(eu_valid_i && eu_tag_in_table && !reuse_existing_entry)
            || (!table_valid_d[eu_match_index]))
            else $error("EU tag %d is not being freed from the register table", eu_tag_i);

        /// Check Insert Logic
        logic [$clog2(NumTags)-1:0] insert_index;
        always_comb begin : find_insert_index
            insert_index = '0;
            for (int entry = 0; entry < NumTags; entry++) begin
                if (!table_valid_q[entry]) begin
                    insert_index = entry[$clog2(NumTags)-1:0];
                    break;
                end
            end
        end : find_insert_index

        // If inserting and space available and not reusing existing entry, then an entry must be allocated
        assert property (@(posedge clk_i) disable iff(!rst_ni)
            !(insert_i && space_available_o && !reuse_existing_entry)
            || table_valid_d[insert_index])
            else $error("Inserting new entry, but entry is not being allocated");

        // Inserting new entry, subwarp_id must be set correctly
        assert property (@(posedge clk_i) disable iff(!rst_ni)
            !(insert_i && space_available_o && !reuse_existing_entry)
            || table_d[insert_index].subwarp_id == subwarp_id_i)
            else $error("Inserting new entry, but subwarp_id is not set correctly");

        // Inserting new entry, dst must be set correctly
        assert property (@(posedge clk_i) disable iff(!rst_ni)
            !(insert_i && space_available_o && !reuse_existing_entry)
            || table_d[insert_index].dst == dst_reg_i)
            else $error("Inserting new entry, but dst register is not set correctly");

        // Inserting new entry, producer tag must be set correctly
        assert property (@(posedge clk_i) disable iff(!rst_ni)
            !(insert_i && space_available_o && !reuse_existing_entry)
            || table_d[insert_index].producer == tag_i)
            else $error("Inserting new entry, but producer tag is not set correctly");

        logic [$clog2(NumTags)-1:0] insert_existing_index;
        always_comb begin : find_insert_existing_index
            insert_existing_index = '0;
            for (int entry = 0; entry < NumTags; entry++) begin
                if (table_valid_q[entry] && table_q[entry].dst == dst_reg_i
                    && table_q[entry].subwarp_id == subwarp_id_i) begin
                    insert_existing_index = entry[$clog2(NumTags)-1:0];
                    break;
                end
            end
        end : find_insert_existing_index

        // If inserting and reusing existing entry, then the existing entry must still be valid
        assert property (@(posedge clk_i) disable iff(!rst_ni)
            !(insert_i && space_available_o && reuse_existing_entry)
            || (table_valid_d[insert_existing_index]))
            else $error("Reusing existing entry, but entry is not marked as valid");

        // If inserting and reusing existing entry, then the existing entry must be updated
        assert property (@(posedge clk_i) disable iff(!rst_ni)
            !(insert_i && space_available_o && reuse_existing_entry)
            || (table_d[insert_existing_index].producer == tag_i))
            else $error("Reusing existing entry, but producer tag is not being updated");

        /// Operand Checks
        for (genvar op = 0; op < OperandsPerInst; op++) begin : gen_assert_operands
            logic operand_from_eu;
            assign operand_from_eu = (eu_valid_i && operands_tag_o[op] == eu_tag_i);

            // If operand has the same tag as EU and EU is valid, then it must be ready
            assert property (@(posedge clk_i) disable iff(!rst_ni)
                !(operand_from_eu) || operands_ready_o[op])
                else $error("Operand %d has tag %d from EU but is not marked as ready",
                    op, operands_tag_o[op]);

            // If operand is in the table and not comming from eu
            logic operand_in_table;
            logic [$clog2(NumTags)-1:0] matching_entry_index;
            always_comb begin : check_operand_in_table
                operand_in_table = 1'b0;
                matching_entry_index = '0;
                for (int entry = 0; entry < NumTags; entry++) begin
                    if (table_valid_q[entry] && table_q[entry].dst == operands_reg_i[op]
                        && table_q[entry].subwarp_id == subwarp_id_i) begin
                        operand_in_table     = 1'b1;
                        matching_entry_index = entry[$clog2(NumTags)-1:0];
                    end
                end
            end : check_operand_in_table

            // Then it must not be ready
            assert property (@(posedge clk_i) disable iff(!rst_ni)
                !(!operand_from_eu && operand_in_table) || (!operands_ready_o[op]))
                else $error("Operand %d with tag %d is marked as ready but is in the table",
                    op, operands_tag_o[op]);

            // Then the tag must be the one from the destinations producer
            assert property (@(posedge clk_i) disable iff(!rst_ni)
                !(!operand_from_eu && operand_in_table)
                || (operands_tag_o[op] == table_q[matching_entry_index].producer))
                else $error("Operand %d has tag %d but should have tag %d from the table",
                    op, operands_tag_o[op], table_q[matching_entry_index].producer);
        end : gen_assert_operands

        /// Sanity Checks of the Table
        // Check that there a no entries with matching destination register or tag
        for (genvar i = 0; i < NumTags; i++) begin : gen_check_entries
            for (genvar j = 0; j < NumTags; j++) begin : gen_check_entries_inner
                // Check destination register
                assert property (@(posedge clk_i) disable iff(!rst_ni) !(table_valid_q[i]
                    && table_valid_q[j] && i != j) || (table_q[i].dst != table_q[j].dst
                    || table_q[i].subwarp_id != table_q[j].subwarp_id))
                else $error("Destination register %d is in multiple entries: %d and %d",
                    table_q[i].dst, i, j);

                // Check producer tag
                assert property (@(posedge clk_i) disable iff(!rst_ni) !(table_valid_q[i]
                    && table_valid_q[j] && i != j) || (table_q[i].producer != table_q[j].producer
                    || table_q[i].subwarp_id != table_q[j].subwarp_id))
                else $error("Producer tag %d is in multiple entries: %d and %d",
                    table_q[i].producer, i, j);
            end : gen_check_entries_inner
        end : gen_check_entries
    `endif

    // #######################################################################################
    // # Formal Properties                                                                   #
    // #######################################################################################

    `ifdef FORMAL
        // All entries are free
        cover property (@(posedge clk_i) disable iff (!rst_ni) table_valid_q == '0);

        // All entries are used
        cover property (@(posedge clk_i) disable iff (!rst_ni) table_valid_q == '1);

        // Insert when space available
        cover property (@(posedge clk_i) disable iff (!rst_ni) insert_i && space_available_o);

        // Insert when no space available
        cover property (@(posedge clk_i) disable iff (!rst_ni) insert_i && !space_available_o);

        // All destination registers written
        cover property (@(posedge clk_i) disable iff (!rst_ni) all_dst_written_o);
        cover property (@(posedge clk_i) disable iff (!rst_ni) !all_dst_written_o);

        // Responses from Execution Unit
        cover property (@(posedge clk_i) disable iff (!rst_ni) eu_valid_i);

        // Reusing existing entry
        cover property (@(posedge clk_i) disable iff (!rst_ni) insert_i && reuse_existing_entry);

        // Inserting new entry
        cover property (@(posedge clk_i) disable iff (!rst_ni) insert_i && !reuse_existing_entry);

        // Operands ready
        for (genvar op = 0; op < OperandsPerInst; op++) begin : gen_cover_operands_ready
            cover property (@(posedge clk_i) disable iff (!rst_ni) operands_ready_o[op]);
            cover property (@(posedge clk_i) disable iff (!rst_ni) !operands_ready_o[op]);
        end : gen_cover_operands_ready

        // Assume that we only insert unique tags -> tag_i is not in table when insert_i is high
        logic insert_tag_in_table;
        always_comb begin : assume_insert_tag_in_table
            insert_tag_in_table = 1'b0;
            for (int entry = 0; entry < NumTags; entry++) begin
                if (table_valid_q[entry] && table_q[entry].producer == tag_i) begin
                    insert_tag_in_table = 1'b1;
                end
            end
        end : assume_insert_tag_in_table

        // Assume that we never successfully insert a tag that is already in the table
        assume property (@(posedge clk_i) disable iff (!rst_ni)
            !(insert_i && space_available_o) || !(insert_tag_in_table))
            else $error("Assumption failed: Inserting tag %d that is already in the table", tag_i);
    `endif
endmodule : reg_table
