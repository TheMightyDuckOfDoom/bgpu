// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "common_cells/registers.svh"

/// Accepts a request and splits it into multiple coalesced sub-requests.
// Finds the first active thread and uses its address for the new request
// Any thread within the same block uses the same sub-request
// This is repeated untile all threads have been part of a sub-request
module coalesce_splitter #(
    /// Number of parallel requests, usually the warp width
    parameter int unsigned NumRequests = 4,
    /// Memory Address width in bits
    parameter int unsigned AddressWidth = 32,
    /// Memory Block size in bytes -> Memory request width
    parameter int unsigned BlockIdxBits = 4,
    /// Width of the ID that is common for all sub-requests
    parameter int unsigned CommonReqIdWidth = 1,
    /// Warp Data
    parameter type warp_data_t = logic,
    /// Write width
    parameter type write_width_t = logic,

    /// Dependent parameter, do **not** overwrite.
    parameter int unsigned SubReqIdWidth = NumRequests > 1 ? $clog2(NumRequests) : 1,
    parameter type com_req_id_t    = logic       [CommonReqIdWidth-1:0],
    parameter type sub_req_id_t    = logic       [SubReqIdWidth-1:0],
    parameter type addr_t          = logic       [AddressWidth-1:0],
    parameter type req_addr_t      = addr_t      [NumRequests-1:0],
    parameter type valid_mask_t    = logic       [NumRequests-1:0],
    parameter type block_idx_t     = logic       [BlockIdxBits-1:0],
    parameter type block_offsets_t = block_idx_t [NumRequests-1:0],
    parameter type block_addr_t    = logic       [AddressWidth-BlockIdxBits-1:0]
) (
    /// Clock and reset
    input logic clk_i,
    input logic rst_ni,

    /// Insert new request
    output logic         ready_o,
    input  logic         valid_i,
    input  logic         we_i,
    input  com_req_id_t  req_id_i,
    input  valid_mask_t  addr_valid_i,
    input  req_addr_t    addr_i,
    input  warp_data_t   wdata_i,
    input  write_width_t write_width_i,

    /// Send out coalesced requests
    input  logic           req_ready_i,
    output valid_mask_t    req_valid_o,
    output logic           req_we_o,
    output com_req_id_t    req_com_id_o,
    output sub_req_id_t    req_sub_id_o,
    output block_addr_t    req_addr_o,
    output block_offsets_t req_offsets_o,
    output warp_data_t     req_wdata_o,
    output write_width_t   req_write_width_o
);
    // #######################################################################################
    // # Type Definitions                                                                    #
    // #######################################################################################

    // Requests to be coalesced
    typedef struct packed {
        valid_mask_t  req_valid;
        req_addr_t    req_addr;
        com_req_id_t  com_req_id;
        sub_req_id_t  sub_req_id;
        logic         we;
        warp_data_t   wdata;
        write_width_t write_width;
    } state_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Internal state
    state_t state_q, state_d;

    // #######################################################################################
    // # Combinational logic                                                                 #
    // #######################################################################################

    always_comb begin : comb_logic
        // Default
        state_d = state_q;

        // Output handshake
        if ((|req_valid_o) && req_ready_i) begin : output_handshake
            // Update the valid mask -> remove the requests that we sent out
            state_d.req_valid = state_q.req_valid & ~req_valid_o;
            // Increment the sub-request ID for the next request
            state_d.sub_req_id = state_q.sub_req_id + 'd1;
        end : output_handshake

        // Insert handshake
        if (valid_i && ready_o) begin : insert_handshake
            state_d.req_valid   = addr_valid_i;
            state_d.req_addr    = addr_i;
            state_d.we          = we_i;
            state_d.wdata       = wdata_i;
            state_d.write_width = write_width_i;
            state_d.com_req_id  = req_id_i;
            state_d.sub_req_id  = '0; // First sub-request
        end : insert_handshake

    end : comb_logic

    // We are ready to accept a new request if we have no valid requests pending
    // Or we just sent out the last request
    assign ready_o = !(|state_q.req_valid) || (|req_valid_o) && req_ready_i
        && !(|(state_q.req_valid & ~req_valid_o));

    // Output request IDs
    assign req_com_id_o = state_q.com_req_id;
    assign req_sub_id_o = state_q.sub_req_id;

    // Output write enable, data and width
    assign req_we_o          = state_q.we;
    assign req_wdata_o       = state_q.wdata;
    assign req_write_width_o = state_q.write_width;

    // #######################################################################################
    // # Coalesce Comparator                                                                 #
    // #######################################################################################

    coalesce_comparator #(
        .AddressWidth( AddressWidth ),
        .NumRequests ( NumRequests  ),
        .BlockIdxBits( BlockIdxBits )
    ) i_coalesce_comparator (
        .req_valid_i( state_q.req_valid ),
        .req_addr_i ( state_q.req_addr  ),

        .coalesced_addr_o      ( req_addr_o    ),
        .members_o             ( req_valid_o   ),
        .member_block_offsets_o( req_offsets_o )
    );

    // #######################################################################################
    // # Sequential logic                                                                    #
    // #######################################################################################

    `FF(state_q, state_d, '0, clk_i, rst_ni);

endmodule : coalesce_splitter
