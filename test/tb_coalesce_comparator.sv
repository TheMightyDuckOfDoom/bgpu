// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Testbench for Coalesce Comparator
module tb_coalesce_comparator #(
    // Simulation parameters
    parameter int unsigned RequestsToCoalesce = 10000,

    // Simulation time parameters
    parameter time ClkPeriod = 10ns,
    parameter time ApplDelay = 1ns,
    parameter time AcqDelay  = 8ns,

    /// Number of inflight instructions per warp
    parameter int unsigned AddressWidth = 12,
    // Number of requests to coalesce at the same time
    parameter int unsigned NumRequests = 8,
    // Block size in bytes
    parameter int unsigned BlockIdxbits = 8
) ();

    // #######################################################################################
    // # Local Parameters                                                                    #
    // #######################################################################################

    localparam int unsigned ReqWidth = (AddressWidth + 1) * NumRequests;

    // #######################################################################################
    // # Type Definitions                                                                    #
    // #######################################################################################

    typedef logic [AddressWidth-BlockIdxbits-1:0] block_addr_t;
    typedef logic [AddressWidth-1:0] addr_t;
    typedef logic [BlockIdxbits-1:0] block_offset_t;

    typedef struct packed {
        logic  [NumRequests-1:0] valid;
        addr_t [NumRequests-1:0] addr;
    } req_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Inputs
    req_t req;

    // Outputs
    logic          [NumRequests-1:0] members;
    block_offset_t [NumRequests-1:0] member_block_offsets;
    block_addr_t                     coalesced_addr;

    // #######################################################################################
    // # DUT Instantiation                                                                   #
    // #######################################################################################

    coalesce_comparator #(
        .AddressWidth( AddressWidth ),
        .NumRequests ( NumRequests  ),
        .BlockIdxBits( BlockIdxbits )
    ) i_coalesce_comparator (
        .req_valid_i( req.valid ),
        .req_addr_i ( req.addr  ),

        .coalesced_addr_o      ( coalesced_addr       ),
        .members_o             ( members              ),
        .member_block_offsets_o( member_block_offsets )
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
        return;
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
    endfunction

    initial begin
        int unsigned coalesced_match_count;
        for(int i = 0; i < RequestsToCoalesce; i++) begin
            // Randomize the request
            randomize_req();

            // Check the output
            $display("Request %0d", i);
            for(int j = 0; j < NumRequests; j++) begin
                $display("  Valid: %0d, Address: %0h", req.valid[j], req.addr[j]);
            end

            #1ns;

            $display("  Coalesced Address: %0h", coalesced_addr);
            for(int j = 0; j < NumRequests; j++) begin
                $display("  Member %0d: Valid: %0d, Offset: %0h", j, members[j],
                    member_block_offsets[j]);
            end

            assert((|req.valid) -> ($countones(members) > 0))
                else $error("No members found for valid request");

            assert(req.valid == '0 -> members == '0)
                else $error("Members should be zero for invalid requests");

            coalesced_match_count = 0;
            for(int j = 0; j < NumRequests; j++) begin
                // Check the block offsets
                assert(member_block_offsets[j] == req.addr[j][BlockIdxbits-1:0])
                    else $error("Member block offset %0h does not match request address %0h",
                        member_block_offsets[j], req.addr[j][BlockIdxbits-1:0]);

                assert(req.valid[j] && req.addr[j][AddressWidth-1:BlockIdxbits] == coalesced_addr
                        -> members[j])
                    else $error("Member %0d is in coalesced address %0h, but members[%0d] is %0d",
                        j, coalesced_addr, j, members[j]);

                assert(req.valid[j] && req.addr[j][AddressWidth-1:BlockIdxbits] != coalesced_addr
                        -> !members[j])
                    else $error("Member %0d is not in coalesced addr %0h, but members[%0d] is %0d",
                        j, coalesced_addr, j, members[j]);

                if (req.valid[j] && req.addr[j][AddressWidth-1:BlockIdxbits] == coalesced_addr)
                begin
                    coalesced_match_count++;
                end
            end

            if (|req.valid) begin
                assert(coalesced_match_count > 0)
                    else $error("No requests matched the coalesced address %0h", coalesced_addr);
            end else begin
                assert(coalesced_match_count == 0)
                    else $error("Requests matched the coalesced addr, but no valid reqs were given",
                        coalesced_addr);
            end
        end

        $finish();
    end

endmodule : tb_coalesce_comparator
