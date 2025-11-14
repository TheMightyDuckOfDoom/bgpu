// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "common_cells/registers.svh"

/// Register Table
// Maps a register to a tag that produces the most recent value
module reg_table #(
    /// Number of instructions to fetch for the warp
    parameter int unsigned FetchWidth = 2,
    /// Number of instructions that can write back simultaneously
    parameter int unsigned WritebackWidth = 2,
    /// Number of inflight instructions
    parameter int unsigned NumTags = 4,
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
    // # Local Parameters                                                                    #
    // #######################################################################################

    localparam int unsigned IdxWidth = NumTags > 1 ? $clog2(NumTags) : 1;

    // #######################################################################################
    // # Typedefs                                                                            #
    // #######################################################################################

    // Register Table Entry
    typedef struct packed {
        subwarp_id_t subwarp_id;
        reg_idx_t    dst;
        tag_t        producer;
    } reg_table_entry_t;

    // Register Table Index Type
    typedef logic [IdxWidth-1:0] index_t;

    // Table Mask Type
    typedef logic [ NumTags-1:0] table_mask_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Register Table
    table_mask_t table_valid_q, table_valid_d;
    reg_table_entry_t [NumTags-1:0] table_q, table_d;

    // Index where to insert next for each fetch
    index_t [FetchWidth-1:0] insert_index;

    // Temporary valid mask for insert logic
    table_mask_t previous_inserts;

    // Reuse existing entry when inserting
    logic [FetchWidth-1:0] reuse_existing_entry, insert_possible;

    // ######################################################################
    // # Combinational Logic                                                #
    // ######################################################################

    // All destination registers written if no entry is valid
    assign all_dst_written_o = table_valid_q == '0;

    // Determine if operand is ready and its tag
    always_comb begin : operand_check_logic
        // Default
        operands_ready_o = '1;
        operands_tag_o   = '0;

        // Loop FetchWidth
        for (int fidx = 0; fidx < FetchWidth; fidx++) begin : loop_fetch_width
            // Check each operand
            for (int op = 0; op < OperandsPerInst; op++) begin : check_operand
                // Check all entries, if valid and the destination is the same as the operand
                // and part of the same subwarp |-> not ready, return tag
                for (int entry = 0; entry < NumTags; entry++) begin : check_entry
                    if (table_valid_q[entry] && table_q[entry].dst == operands_reg_i[fidx][op]
                        && table_q[entry].subwarp_id == subwarp_id_i) begin : entry_found
                        // Not ready, return tag
                        operands_ready_o[fidx][op] = 1'b0;
                        operands_tag_o  [fidx][op] = table_q[entry].producer;
                        break;
                    end : entry_found
                end : check_entry

                // Check if operand is produced by a previous instruction in the same fetch
                for (int prev_fidx = 0; prev_fidx < fidx; prev_fidx++) begin : check_prev_fetch
                    if (dst_reg_i[prev_fidx] == operands_reg_i[fidx][op])
                    begin : prev_fidx_dependency
                        operands_ready_o[fidx][op] = 1'b0;
                        operands_tag_o  [fidx][op] = tag_i[prev_fidx];
                    end : prev_fidx_dependency
                end : check_prev_fetch

                // Check if operand is produced by the EUs in the same cycle |-> then it is ready
                for (int wb = 0; wb < WritebackWidth; wb++) begin : check_eu
                    if (eu_valid_i[wb] && eu_tag_i[wb] == operands_tag_o[fidx][op]) begin
                        operands_ready_o[fidx][op] = 1'b1;
                    end
                end : check_eu
            end : check_operand
        end : loop_fetch_width
    end : operand_check_logic

    // Find insert index for each fetch
    always_comb begin : find_insert_indices
        previous_inserts     = '0;
        insert_index         = '0;
        reuse_existing_entry = '0;
        insert_possible      = '0;

        // Loop over FetchWidth
        for (int fidx = 0; fidx < FetchWidth; fidx++) begin : loop_fetch_width
            // First check if we have an existing entry for this destination
            for (int entry = 0; entry < NumTags; entry++) begin : check_existing_entries
                if (table_valid_q[entry] && table_q[entry].dst == dst_reg_i[fidx]
                    && table_q[entry].subwarp_id == subwarp_id_i) begin : modify_existing
                    // Insert into existing entry
                    insert_index[fidx] = index_t'(entry);
                    // Mark as reusing existing entry
                    reuse_existing_entry[fidx] = 1'b1;
                    // Mark as possible to insert
                    insert_possible[fidx] = 1'b1;
                    // Subsequent inserts could also overwrite this entry
                    break;
                end : modify_existing
            end : check_existing_entries

            // Then check if we match a previous fetch that allocated an entry
            for (int prev_fidx = 0; prev_fidx < fidx; prev_fidx++) begin : check_previous_fetches
                if (insert_i[prev_fidx] && dst_reg_i[prev_fidx] == dst_reg_i[fidx])
                begin : previous_fetch_match
                    // Insert into existing entry from previous fetch
                    insert_index[fidx] = insert_index[prev_fidx];
                    // Mark as reusing existing entry
                    reuse_existing_entry[fidx] = 1'b1;
                    // Mark as possible to insert
                    insert_possible[fidx] = 1'b1;
                    // Subsequent inserts could also overwrite this entry
                    break;
                end : previous_fetch_match
            end : check_previous_fetches

            // If not reusing existing entry, find a free entry
            if (!reuse_existing_entry[fidx]) begin : free_entry_needed
                for (int entry = 0; entry < NumTags; entry++) begin : find_free_entry
                    if (!table_valid_q[entry] && !previous_inserts[entry]) begin : free_entry_found
                        // Insert into this free entry
                        insert_index[fidx] = index_t'(entry);
                        // Mark as used during this cycle
                        previous_inserts[entry] = 1'b1;
                        // Mark as possible to insert
                        insert_possible[fidx] = 1'b1;
                        break;
                    end : free_entry_found
                end : find_free_entry
            end : free_entry_needed
        end : loop_fetch_width
    end : find_insert_indices

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
            // Insert into table
            if (insert_i[fidx] && insert_possible[fidx]) begin : insert_logic
                // Mark as valid, as we could have deallocated it in this cycle
                table_valid_d[insert_index[fidx]] = 1'b1;

                // Update the entry
                table_d[insert_index[fidx]].dst        = dst_reg_i[fidx];
                table_d[insert_index[fidx]].producer   = tag_i    [fidx];
                table_d[insert_index[fidx]].subwarp_id = subwarp_id_i;
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

    `ifndef SYNTHESIS
        // If an operand of a fetch is a previous fetch's destination,
        // then the operands tag must be the previous fetch's tag
        for (genvar fidx = 0; fidx < FetchWidth; fidx++) begin : gen_check_prev_fetch_operand_tags
            for (genvar op = 0; op < OperandsPerInst; op++) begin : gen_check_operand
                index_t prev_fetch_index;
                logic   prev_fetch_found;

                always_comb begin : check_prev_fetch
                    prev_fetch_found = 1'b0;
                    prev_fetch_index = '0;
                    for (int prev_fidx = 0; prev_fidx < fidx; prev_fidx++) begin
                        if (dst_reg_i[prev_fidx] == operands_reg_i[fidx][op]) begin
                            prev_fetch_found = 1'b1;
                            prev_fetch_index = index_t'(prev_fidx);
                        end
                    end
                end : check_prev_fetch

                // If previous fetch found, then tag must match
                assert property (@(posedge clk_i) disable iff(!rst_ni)
                    !(insert_i[fidx] && prev_fetch_found)
                    || (operands_tag_o[fidx][op] == tag_i[prev_fetch_index]))
                    else $error("%d: Operand %d tag %d does not match previous fetch tag %d",
                        fidx, op, operands_tag_o[fidx][op],
                        tag_i[prev_fetch_index]);

                // If previous fetch found, then operand is not ready
                assert property (@(posedge clk_i) disable iff(!rst_ni)
                    !(insert_i[fidx] && prev_fetch_found) || (!operands_ready_o[fidx][op]))
                    else $error("%d: Operand %d is marked as ready but comes from previous fetch",
                        fidx, op);
            end : gen_check_operand
        end : gen_check_prev_fetch_operand_tags

        // If all_dst_written_o is high, then no entries must be valid
        assert property (@(posedge clk_i) disable iff(!rst_ni)
            !(all_dst_written_o) || (table_valid_q == '0))
            else $error("all_dst_written_o is high, but some entries are still occupied");

        /// Check EU responses
        // Check if eu tag is in the table
        index_t [WritebackWidth-1:0] eu_match_index;
        logic   [WritebackWidth-1:0] eu_tag_in_table;
        logic   [WritebackWidth-1:0] eu_deallocating;
        always_comb begin : check_eu_tag_in_table
            eu_match_index  = '0;
            eu_tag_in_table = '0;
            eu_deallocating = '1;
            for (int wb = 0; wb < WritebackWidth; wb++) begin : wb_loop
                for (int entry = 0; entry < NumTags; entry++) begin
                    if (table_valid_q[entry] && table_q[entry].producer == eu_tag_i[wb]) begin
                        eu_tag_in_table[wb] = 1'b1;
                        eu_match_index [wb] = entry[$clog2(NumTags)-1:0];
                    end
                end

                // Check if Fetch is reallocating this entry
                for (int fidx = 0; fidx < FetchWidth; fidx++) begin : check_fetch_reallocating
                    if (insert_i[fidx] && insert_index[fidx] == eu_match_index[wb]) begin
                        eu_deallocating[wb] = 1'b0;
                    end
                end : check_fetch_reallocating
            end : wb_loop
        end : check_eu_tag_in_table

        // If EU valid and is in the table, then it mus be freed if it is not reused
        for (genvar wb = 0; wb < WritebackWidth; wb++) begin : gen_assert_eu_responses
            assert property (@(posedge clk_i) disable iff(!rst_ni)
                !(eu_valid_i[wb] && eu_tag_in_table[wb] && eu_deallocating[wb])
                || (!table_valid_d[eu_match_index[wb]]))
                else $error("EU %d tag %d is not being freed from the register table", wb,
                    eu_tag_i[wb]);
        end : gen_assert_eu_responses

        for (genvar fidx = 0; fidx < FetchWidth; fidx++) begin : gen_check_insert
            // Inserting possible
            assert property (@(posedge clk_i) disable iff(!rst_ni)
                !(insert_i[fidx]) || insert_possible[fidx])
                else $error("%d: Inserting entry, but insert not possible (table full?)", fidx);

            // Check that insert_i is continous
            if (fidx > 0) begin : gen_check_insert_continuous
                assert property (@(posedge clk_i) disable iff(!rst_ni)
                    !insert_i[fidx] || insert_i[fidx-1])
                else $error("Insert signal is not continuous at fetch index %d: %b", fidx,
                    insert_i);
            end : gen_check_insert_continuous

            // If inserting, then the inserted entry must be marked as valid
            assert property (@(posedge clk_i) disable iff(!rst_ni)
                !insert_i[fidx] || table_valid_d[insert_index[fidx]])
                else $error("%d: Inserting entry, but entry is not being allocated", fidx);

            // Check if any subsequent fetch is overwriting the same entry
            logic subsequent_overwrite;
            always_comb begin : check_subsequent_overwrite
                subsequent_overwrite = 1'b0;
                for (int next_fidx = fidx + 1; next_fidx < FetchWidth; next_fidx++) begin
                    if (insert_i[next_fidx] && insert_index[next_fidx] == insert_index[fidx]) begin
                        subsequent_overwrite = 1'b1;
                        assert(reuse_existing_entry[next_fidx])
                        else $error("%d: Fetch %d overwrites the same entry with reusing it",
                            fidx, next_fidx);
                    end
                end
            end : check_subsequent_overwrite

            for (genvar other_fidx = 0; other_fidx < FetchWidth; other_fidx++)
            begin : gen_assert_fidx
                if (other_fidx != fidx) begin : gen_check_different_fetch_indices
                    // If inserting and both not reusing existing entry, then indices must be different
                    assert property (@(posedge clk_i) disable iff(!rst_ni)
                        !(insert_i[fidx] && insert_i[other_fidx]
                            && !reuse_existing_entry[fidx]
                            && !reuse_existing_entry[other_fidx])
                        || (insert_index[fidx] != insert_index[other_fidx]))
                        else $error("%d and %d: Inserting new entries into the same index %d",
                            fidx, other_fidx, insert_index[fidx]);
                end : gen_check_different_fetch_indices
            end : gen_assert_fidx

            // Inserting new entry, subwarp_id must be set correctly
            assert property (@(posedge clk_i) disable iff(!rst_ni)
                !(insert_i[fidx] && !reuse_existing_entry[fidx])
                || table_d[insert_index[fidx]].subwarp_id == subwarp_id_i)
                else $error("%d: Inserting new entry, but subwarp_id is not set correctly", fidx);

            // Inserting new entry, dst must be set correctly
            assert property (@(posedge clk_i) disable iff(!rst_ni)
                !(insert_i[fidx] && !reuse_existing_entry[fidx])
                || table_d[insert_index[fidx]].dst == dst_reg_i[fidx])
                else $error("%d: Inserting new entry, but dst register is not set correctly", fidx);

            // Inserting new entry, producer tag must be set correctly
            // If we are inserting a new entry and no subsequent fetch is overwriting it
            assert property (@(posedge clk_i) disable iff(!rst_ni)
                !(insert_i[fidx] && !reuse_existing_entry[fidx] && !subsequent_overwrite)
                || table_d[insert_index[fidx]].producer == tag_i[fidx])
                else $error("%d: Inserting new entry, but producer tag is not correct", fidx);

            /// Operand Checks
            for (genvar op = 0; op < OperandsPerInst; op++) begin : gen_assert_operands
                // Does the operand come from the EU in this cycle?
                logic operand_from_eu;
                always_comb begin : check_operand_from_eu
                    operand_from_eu = 1'b0;
                    for (int wb = 0; wb < WritebackWidth; wb++) begin
                        if (eu_valid_i[wb] && operands_tag_o[fidx][op] == eu_tag_i[wb]) begin
                            operand_from_eu = 1'b1;
                        end
                    end
                end : check_operand_from_eu

                // If operand has the same tag as EU and EU is valid, then it must be ready
                // |-> comes from EU in this cycle
                assert property (@(posedge clk_i) disable iff(!rst_ni)
                    !(operand_from_eu) || operands_ready_o[fidx][op])
                    else $error("%d: Operand %d has tag %d from EU but is not marked as ready",
                        fidx, op, operands_tag_o[fidx][op]);

                // If operand is in the table and not coming from EU
                logic   operand_in_table;
                index_t operand_in_table_index;
                always_comb begin : check_operand_in_table
                    operand_in_table       = 1'b0;
                    operand_in_table_index = '0;
                    for (int entry = 0; entry < NumTags; entry++) begin
                        if (table_valid_q[entry] && table_q[entry].dst == operands_reg_i[fidx][op]
                            && table_q[entry].subwarp_id == subwarp_id_i) begin
                            operand_in_table       = 1'b1;
                            operand_in_table_index = index_t'(entry);
                        end
                    end

                    // If it comes from EU, then it is no longer in the table
                    if (operand_from_eu) begin
                        operand_in_table = 1'b0;
                    end
                end : check_operand_in_table

                // Then it must not be ready
                assert property (@(posedge clk_i) disable iff(!rst_ni)
                    !operand_in_table || (!operands_ready_o[fidx][op]))
                    else $error("%d: Operand %d with tag %d is marked as ready but is in the table",
                        fidx, op, operands_tag_o[fidx][op]);
            end : gen_assert_operands
        end : gen_check_insert

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
        /// Cover Properties
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
                cover property (@(posedge clk_i) disable iff (!rst_ni)
                    operands_ready_o[fetch_idx][op]);
                cover property (@(posedge clk_i) disable iff (!rst_ni)
                    !operands_ready_o[fetch_idx][op]);
            end : gen_cover_operands_ready
        end : gen_cover_inserts

        // Insert full width
        cover property (@(posedge clk_i) disable iff (!rst_ni) insert_i == '1);

        /// Assumptions on Inputs
        // Check if insert tags are already in the table
        logic [FetchWidth-1:0] insert_tag_already_in_table;
        always_comb begin : assume_insert_tag_already_in_table
            insert_tag_already_in_table = '0;
            for (int fidx = 0; fidx < FetchWidth; fidx++) begin
                for (int entry = 0; entry < NumTags; entry++) begin
                    if (table_valid_q[entry] && table_q[entry].producer == tag_i[fidx]) begin
                        insert_tag_already_in_table[fidx] = 1'b1;
                    end
                end
            end
        end : assume_insert_tag_already_in_table

        // Calculate current table occupancy
        int unsigned current_table_occupancy;
        always_comb begin : calculate_table_occupancy
            current_table_occupancy = 0;
            for (int entry = 0; entry < NumTags; entry++) begin
                if (table_valid_q[entry]) begin
                    current_table_occupancy = current_table_occupancy + 1;
                end
            end
        end : calculate_table_occupancy

        // Loop over FetchWidth
        for (genvar fidx = 0; fidx < FetchWidth; fidx++) begin : gen_assume_insert_tags
            // Assume that we never successfully insert a tag that is already in the table
            assume property (@(posedge clk_i) disable iff (!rst_ni)
                !(insert_i[fidx]) || !(insert_tag_already_in_table[fidx]))
                else $error("Assumption failed: Inserting tag %d that is already in the table",
                    tag_i[fidx]);

            // Assume that we insert only unique tags within the same fetch
            for (genvar prev_fidx = 0; prev_fidx < fidx; prev_fidx++) begin : gen_assume_unique
                assume property (@(posedge clk_i) disable iff (!rst_ni)
                    !(insert_i[fidx] && insert_i[prev_fidx])
                    || (tag_i[fidx] != tag_i[prev_fidx]))
                    else $error("Assume failed: Inserting duplicate tags %d within fetch",
                        tag_i[fidx]);
            end : gen_assume_unique

            // Assume that eu tags never match inserted tags
            for (genvar wb = 0; wb < WritebackWidth; wb++) begin : gen_assume_eu_tags
                assume property (@(posedge clk_i) disable iff (!rst_ni)
                    !(insert_i[fidx] && eu_valid_i[wb]) || (eu_tag_i[wb] != tag_i[fidx]))
                    else $error("Assume failed: Inserting tag %d that matches EU tag %d",
                        tag_i[fidx], eu_tag_i[wb]);
            end : gen_assume_eu_tags

            // Assume insert_i is continuous
            if (fidx > 0) begin : gen_assume_insert_continuous
                assume property (@(posedge clk_i) disable iff (!rst_ni)
                    !insert_i[fidx] || insert_i[fidx-1])
                    else $error("Assume failed: insert_i is not continuous at fidx %d: %b",
                        fidx, insert_i);
            end : gen_assume_insert_continuous

            // Assume that we never insert more tags than there are free entries
            assume property (@(posedge clk_i) disable iff (!rst_ni)
                !(insert_i[fidx]) || ((current_table_occupancy + fidx) < NumTags))
                else $error("Assume failed: Inserting at fidx %d would overflow the table",
                    fidx);
        end : gen_assume_insert_tags
    `endif
endmodule : reg_table
