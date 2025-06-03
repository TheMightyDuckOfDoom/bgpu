// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Coalsce Comparator
// Finds the first common block address of a set of requests
module coalesce_comparator #(
    // Width of the address
    parameter int unsigned AddressWidth = 32,
    // Number of requests to coalesce
    parameter int unsigned NumRequests = 8,
    // Block size in bytes
    parameter int unsigned BlockIdxBits = 6,

    /// Dependent parameter, do **not** overwrite.
    parameter type block_addr_t = logic [AddressWidth-BlockIdxBits-1:0],
    parameter type addr_t       = logic [             AddressWidth-1:0],
    parameter type block_idx_t  = logic [             BlockIdxBits-1:0]
) (
    // Is the request address valid?
    input  logic  [NumRequests-1:0] req_valid_i,
    // Request addresses
    input  addr_t [NumRequests-1:0] req_addr_i,

    // Address to which the requests are coalesced
    output block_addr_t coalesced_addr_o,
    // Mask indicating which requests are within the coalesced address
    output logic       [NumRequests-1:0] members_o,
    // Offsets for each request relative to the coalesced address
    output block_idx_t [NumRequests-1:0] member_block_offsets_o
);
    // Find the first valid address within the request
    always_comb begin : find_first_valid_block
        coalesced_addr_o = '0;
        for (int i = 0; i < NumRequests; i++) begin
            if (req_valid_i[i]) begin
                // Align the address to the block size -> throw away the block index bits
                coalesced_addr_o = req_addr_i[i][AddressWidth-1:BlockIdxBits];
                break;
            end
        end
    end : find_first_valid_block

    // Check if an address is within first_valid_block
    always_comb begin : check_members
        members_o = '0;
        for (int i = 0; i < NumRequests; i++) begin
            if (req_valid_i[i] && req_addr_i[i][AddressWidth-1:BlockIdxBits]
                    == coalesced_addr_o) begin
                members_o[i] = 1'b1;
            end
        end
    end : check_members

    // Assign the block offsets for each request
    for(genvar i = 0; i < NumRequests; i++) begin : gen_member_block_offsets
        assign member_block_offsets_o[i] = req_addr_i[i][BlockIdxBits-1:0];
    end : gen_member_block_offsets

endmodule : coalesce_comparator
