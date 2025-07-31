// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "common_cells/registers.svh"

/// Thread Dispatcher
// Dispatches thread blocks to the compute clusters
module thread_dispatcher #(
    /// Width of the Program Counter
    parameter int unsigned PcWidth = 16,
    // Memory Address width in bits
    parameter int unsigned AddressWidth = 32,
    // How many bits are used to index thread blocks inside a thread group?
    parameter int unsigned TblockIdxBits = 8,
    // How many bits are used to identify a thread group?
    parameter int unsigned TgroupIdBits = 8,

    /// Dependent parameter, do **not** overwrite.
    parameter type tblock_idx_t = logic [TblockIdxBits-1:0],
    parameter type tgroup_id_t  = logic [ TgroupIdBits-1:0],
    parameter type addr_t       = logic [ AddressWidth-1:0],
    parameter type pc_t         = logic [      PcWidth-1:0]
) (
    // Clock and reset
    input logic clk_i,
    input logic rst_ni,

    // Request to start dispatching thread blocks
    output logic        ready_o,
    input  logic        start_i,
    input  pc_t         pc_i,
    input  addr_t       dp_addr_i,
    input  tblock_idx_t number_of_tblocks_i,
    input  tgroup_id_t  tgroup_id_i,

    // Interface to start a new thread block -> to compute clusters
    input  logic        warp_free_i, // The is atleas one free warp that can start a new block
    output logic        allocate_warp_o,
    output pc_t         allocate_pc_o,
    output addr_t       allocate_dp_addr_o, // Data / Parameter address
    output tblock_idx_t allocate_tblock_idx_o, // Block index -> used to calculate the thread id
    output tgroup_id_t  allocate_tgroup_id_o, // Block id -> unique identifier for the block

    output tblock_idx_t dispatched_tblocks_o // How many thread blocks have been dispatched
);

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Request
    pc_t         pc_q,                pc_d;
    addr_t       dp_addr_q,           dp_addr_d;
    tblock_idx_t number_of_tblocks_q, number_of_tblocks_d;
    tgroup_id_t  tgroup_id_q,         tgroup_id_d;

    // How many thread blocks have been dispatched for the request?
    tblock_idx_t dispatched_tblocks_q, dispatched_tblocks_d;

    // #######################################################################################
    // # Combinational Logic                                                                 #
    // #######################################################################################

    always_comb begin : main_logic
        // Default
        pc_d                = pc_q;
        dp_addr_d           = dp_addr_q;
        number_of_tblocks_d = number_of_tblocks_q;
        tgroup_id_d         = tgroup_id_q;

        dispatched_tblocks_d = dispatched_tblocks_q;

        ready_o               = 1'b0;
        allocate_warp_o       = 1'b0;
        allocate_pc_o         = '0;
        allocate_dp_addr_o    = '0;
        allocate_tblock_idx_o = '0;
        allocate_tgroup_id_o  = '0;

        // We are ready for a new request if we are not currently dispatching
        if (dispatched_tblocks_q == number_of_tblocks_q) begin : new_request
            ready_o = 1'b1;

            if (start_i) begin : start_request
                // Store the request
                pc_d                = pc_i;
                dp_addr_d           = dp_addr_i;
                number_of_tblocks_d = number_of_tblocks_i;
                tgroup_id_d         = tgroup_id_i;

                dispatched_tblocks_d = '0;
            end : start_request
        end : new_request
        else begin : dispatch_warp
            allocate_warp_o       = 1'b1;
            allocate_pc_o         = pc_q;
            allocate_dp_addr_o    = dp_addr_q;
            allocate_tblock_idx_o = dispatched_tblocks_q;
            allocate_tgroup_id_o  = tgroup_id_q; // Same ID for all tblocks in a group

            // Go to the next block if we can allocate the tblock
            if (warp_free_i) begin : allocate_next_warp
                dispatched_tblocks_d = dispatched_tblocks_q + 'd1;
            end : allocate_next_warp
        end : dispatch_warp
    end : main_logic

    assign dispatched_tblocks_o = dispatched_tblocks_q;

    // #######################################################################################
    // # Sequential Logic                                                                    #
    // #######################################################################################

    // Request
    `FF(pc_q,                pc_d,                '0, clk_i, rst_ni)
    `FF(dp_addr_q,           dp_addr_d,           '0, clk_i, rst_ni)
    `FF(number_of_tblocks_q, number_of_tblocks_d, '0, clk_i, rst_ni)
    `FF(tgroup_id_q,         tgroup_id_d,         '0, clk_i, rst_ni)

    // Number of already dispatched thread blocks
    `FF(dispatched_tblocks_q, dispatched_tblocks_d, '0, clk_i, rst_ni)

endmodule : thread_dispatcher
