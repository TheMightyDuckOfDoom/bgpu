// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "common_cells/registers.svh"

/// Register Table
// Maps a register to a tag that produces the most recent value
module reg_table #(
    /// Number of instructions to fetch for the warp
    parameter int unsigned FetchWidth = 1,
    /// Number of instructions that can write back simultaneously
    parameter int unsigned WritebackWidth = 2,
    /// Number of inflight instructions
    parameter int unsigned NumTags = 2,
    /// Number of threads per warp
    parameter int unsigned WarpWidth = 2,
    /// How many registers can each warp access as operand or destination
    parameter int unsigned RegIdxWidth = 4,
    /// How many operands each instruction can have
    parameter int unsigned OperandsPerInst = 2,

    parameter int unsigned TagWidth       = $clog2(NumTags),
    parameter int unsigned SubwarpIdWidth = WarpWidth > 1 ? $clog2(WarpWidth) : 1,
    parameter type         tag_t          = logic     [       TagWidth-1:0],
    parameter type         reg_idx_t      = logic     [    RegIdxWidth-1:0],
    parameter type         subwarp_id_t   = logic     [ SubwarpIdWidth-1:0],
    parameter type         op_mask_t      = logic     [OperandsPerInst-1:0],
    parameter type         op_reg_idx_t   = reg_idx_t [OperandsPerInst-1:0],
    parameter type         op_tag_t       = tag_t     [OperandsPerInst-1:0]
) (
    /// Clock and Reset
    input logic clk_i,
    input logic rst_ni,

    /// To Fetcher -> Are all registers written to register file?
    // -> no pending instruction
    output logic all_dst_written_o,

    // From Decoder
    input  subwarp_id_t subwarp_id_i,
    input  logic        [FetchWidth-1:0] insert_i,
    input  tag_t        [FetchWidth-1:0] tag_i,
    input  reg_idx_t    [FetchWidth-1:0] dst_reg_i,
    input  op_reg_idx_t [FetchWidth-1:0] operands_reg_i,

    // To Wait Buffer
    output op_mask_t [FetchWidth-1:0] operands_ready_o,
    output op_tag_t  [FetchWidth-1:0] operands_tag_o,

    // From Execution Unit
    input logic [WritebackWidth-1:0] eu_valid_i,
    input tag_t [WritebackWidth-1:0] eu_tag_i
);

    // #######################################################################################
    // # Typedefs                                                                            #
    // #######################################################################################

    // Register Table Entry
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

    // ######################################################################
    // # Combinational Logic                                                #
    // ######################################################################

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
            for (int wb = 0; wb < WritebackWidth; wb++) begin : check_eu
                if (eu_valid_i[wb] && eu_tag_i[wb] == operands_tag_o[op]) begin
                    operands_ready_o[op] = 1'b1;
                end
            end : check_eu
        end : check_operand
    end : operand_check_logic

    // Register Table Logic
    always_comb begin : reg_table_logic
        // Default
        table_valid_d = table_valid_q;
        table_d       = table_q;


        // Clear logic
        // |-> if the EU is valid, clear all entries with the same producer tag, as result is in register file
        for (int wb = 0; wb < WritebackWidth; wb++) begin : wb_loop
            if (eu_valid_i[wb]) begin : clear_entry
                for (int entry = 0; entry < NumTags; entry++) begin
                    if (table_valid_q[entry] && table_q[entry].producer == eu_tag_i[wb]) begin
                        table_valid_d[entry] = 1'b0;
                    end
                end
            end : clear_entry
        end : wb_loop

        // Insert logic
        for (int fidx = 0; fidx < FetchWidth; fidx++) begin : loop_fetch_width
            // Temporary signal to track if we use an existing entry for this fetch index
            reuse_existing_entry = 1'b0;
            
            // Default outputs
            operands_ready_o[fidx] = '0;
            operands_tag_o  [fidx] = '0;

            // Insert into table
            if (insert_i[fidx]) begin : insert_logic
                // First check operands
                for (int op = 0; op < OperandsPerInst; op++) begin : check_operand
                    // Assume ready
                    operands_ready_o[fidx][op] = 1'b1;
                    // Check all entries, if valid and the destination in the table is the same as the operand
                    // and part of the same subwarp |-> not ready
                    for (int entry = 0; entry < NumTags; entry++) begin : check_entry
                        if (table_valid_q[entry] && table_q[entry].dst == operands_reg_i[fidx][op]
                            && table_q[entry].subwarp_id == subwarp_id_i) begin : entry_found
                            operands_ready_o[fidx][op] = 1'b0;
                            operands_tag_o  [fidx][op] = table_q[entry].producer;
                            break;
                        end : entry_found
                    end : check_entry

                    // Check previous dst in the same FetchWidth and use its tag if there is a dependency
                    for (int prev_fidx = 0; prev_fidx < fidx; prev_fidx++) begin : check_prev_fetch
                        if (dst_reg_i[prev_fidx] == operands_reg_i[fidx][op]) begin : prev_fidx_dependency
                            operands_ready_o[fidx][op] = 1'b0;
                            operands_tag_o  [fidx][op] = tag_i[prev_fidx];
                        end : prev_fidx_dependency
                    end : check_prev_fetch

                    // Check if operand is produced by the EUs in the same cycle |-> then it is ready
                    for (int wb = 0; wb < WritebackWidth; wb++) begin : check_wbs
                        if (eu_valid_i[wb] && eu_tag_i[wb] == operands_tag_o[fidx][op]) begin
                            operands_ready_o[fidx][op] = 1'b1;
                        end
                    end : check_wbs
                end : check_operand

                // Insert destination, first check if dst is already in table
                for (int entry = 0; entry < NumTags; entry++) begin : check_existing_entries
                    if (table_valid_q[entry] && table_q[entry].dst == dst_reg_i[fidx]
                        && table_q[entry].subwarp_id == subwarp_id_i) begin : modify_existing
                        // Mark as valid, as we could have deallocated it in this cycle
                        table_valid_d[entry]    = 1'b1;

                        // Update producer tag
                        table_d[entry].producer = tag_i[fidx];
                        reuse_existing_entry      = 1'b1;
                        break;
                    end : modify_existing
                end : check_existing_entries

                // If not, find a free entry
                if (!reuse_existing_entry) begin : use_free_entry
                    for (int entry = 0; entry < NumTags; entry++) begin : find_free_entry
                        if (!table_valid_q[entry]) begin : free_entry_found
                            // Mark as valid
                            table_valid_d[entry] = 1'b1;

                            // Set the entry
                            table_d[entry].dst        = dst_reg_i   [fidx];
                            table_d[entry].producer   = tag_i       [fidx];
                            table_d[entry].subwarp_id = subwarp_id_i;
                            break;
                        end : free_entry_found
                    end : find_free_entry
                end : use_free_entry
            end : insert_logic
        end : loop_fetch_width
    end

    // #######################################################################################
    // # Sequential Logic                                                                    #
    // #######################################################################################

    `FF(table_valid_q, table_valid_d, '0, clk_i, rst_ni)
    `FF(table_q,       table_d,       '0, clk_i, rst_ni)

    // ######################################################################
    // # Assertions                                                         #
    // ######################################################################

    // TODO: Merge: These are not correct
    `ifndef SYNTHESIS_TODO
        // Check that insert_i is continous
        for (genvar fidx = 1; fidx < FetchWidth; fidx++) begin : gen_check_insert
            assert property (@(posedge clk_i) disable iff(!rst_ni)
                insert_i[fidx] |-> insert_i[fidx-1])
            else $error("Insert signal is not continuous at fetch index %d: %b", fidx, insert_i);
        end : gen_check_insert

        // If all_dst_written_o is high, then no entries must be valid
        assert property (@(posedge clk_i) disable iff(!rst_ni)
            !(all_dst_written_o) || (table_valid_q == '0))
            else $error("all_dst_written_o is high, but some entries are still occupied");

        /// Check EU responses
        // Check if eu tag is in the table
        typedef logic [$clog2(NumTags)-1:0] tag_index_t;
        tag_index_t [WritebackWidth-1:0] eu_match_index;
        logic       [WritebackWidth-1:0] eu_tag_in_table;
        always_comb begin : check_eu_tag_in_table
            eu_match_index  = '0;
            eu_tag_in_table = '0;
            for (int wb = 0; wb < WritebackWidth; wb++) begin : wb_loop
                for (int entry = 0; entry < NumTags; entry++) begin
                    if (table_valid_q[entry] && table_q[entry].producer == eu_tag_i[wb]) begin
                        eu_tag_in_table[wb] = 1'b1;
                        eu_match_index [wb] = entry[$clog2(NumTags)-1:0];
                    end
                end
            end : wb_loop
        end : check_eu_tag_in_table

        // If EU valid and is in the table, then it mus be freed if it is not reused
        for (genvar wb = 0; wb < WritebackWidth; wb++) begin : gen_assert_eu_responses
            assert property (@(posedge clk_i) disable iff(!rst_ni)
                !(eu_valid_i[wb] && eu_tag_in_table[wb] && !reuse_existing_entry)
                || (!table_valid_d[eu_match_index[wb]]))
                else $error("EU %d tag %d is not being freed from the register table", wb, eu_tag_i[wb]);
        end : gen_assert_eu_responses

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

        // If inserting and not reusing existing entry, then an entry must be allocated
        assert property (@(posedge clk_i) disable iff(!rst_ni)
            !(insert_i && !reuse_existing_entry)
            || table_valid_d[insert_index])
            else $error("Inserting new entry, but entry is not being allocated");

        // Inserting new entry, subwarp_id must be set correctly
        assert property (@(posedge clk_i) disable iff(!rst_ni)
            !(insert_i && !reuse_existing_entry)
            || table_d[insert_index].subwarp_id == subwarp_id_i)
            else $error("Inserting new entry, but subwarp_id is not set correctly");

        // Inserting new entry, dst must be set correctly
        assert property (@(posedge clk_i) disable iff(!rst_ni)
            !(insert_i && !reuse_existing_entry)
            || table_d[insert_index].dst == dst_reg_i)
            else $error("Inserting new entry, but dst register is not set correctly");

        // Inserting new entry, producer tag must be set correctly
        assert property (@(posedge clk_i) disable iff(!rst_ni)
            !(insert_i && !reuse_existing_entry)
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
            !(insert_i && reuse_existing_entry)
            || (table_valid_d[insert_existing_index]))
            else $error("Reusing existing entry, but entry is not marked as valid");

        // If inserting and reusing existing entry, then the existing entry must be updated
        assert property (@(posedge clk_i) disable iff(!rst_ni)
            !(insert_i && reuse_existing_entry)
            || (table_d[insert_existing_index].producer == tag_i))
            else $error("Reusing existing entry, but producer tag is not being updated");

        /// Operand Checks
        for (genvar op = 0; op < OperandsPerInst; op++) begin : gen_assert_operands
            logic operand_from_eu;
            always_comb begin : check_operand_from_eu
                operand_from_eu = 1'b0;
                for (int wb = 0; wb < WritebackWidth; wb++) begin
                    if (eu_valid_i[wb] && operands_tag_o[op] == eu_tag_i[wb]) begin
                        operand_from_eu = 1'b1;
                    end
                end
            end : check_operand_from_eu

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

        // All destination registers written
        cover property (@(posedge clk_i) disable iff (!rst_ni) all_dst_written_o);
        cover property (@(posedge clk_i) disable iff (!rst_ni) !all_dst_written_o);

        // Responses from Execution Unit
        for (genvar wb = 0; wb < WritebackWidth; wb++) begin : gen_cover_eu_responses
            cover property (@(posedge clk_i) disable iff (!rst_ni) eu_valid_i[wb]);
            cover property (@(posedge clk_i) disable iff (!rst_ni) !eu_valid_i[wb]);
        end : gen_cover_eu_responses

        for (genvar fetch_idx = 0; fetch_idx < FetchWidth; fetch_idx++) begin : gen_cover_inserts
            // Insert
            cover property (@(posedge clk_i) disable iff (!rst_ni) insert_i[fetch_idx]);

            // Operands ready
            for (genvar op = 0; op < OperandsPerInst; op++) begin : gen_cover_operands_ready
                cover property (@(posedge clk_i) disable iff (!rst_ni)  operands_ready_o[fetch_idx][op]);
                cover property (@(posedge clk_i) disable iff (!rst_ni) !operands_ready_o[fetch_idx][op]);
            end : gen_cover_operands_ready
        end : gen_cover_inserts

        // Insert full width
        cover property (@(posedge clk_i) disable iff (!rst_ni) insert_i == '1);

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
