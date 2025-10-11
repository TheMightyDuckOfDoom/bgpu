// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "common_cells/registers.svh"

/// OBI Thread Engine
// Allows dispatching of threads using an OBI interface
module obi_thread_engine #(
    /// Width of the Program Counter
    parameter int unsigned PcWidth = 16,
    // Memory Address width in bits
    parameter int unsigned AddressWidth = 32,
    // How many bits are used to index thread blocks inside a thread group?
    parameter int unsigned TblockIdxBits = 8,
    // How many bits are used to identify a thread group?
    parameter int unsigned TgroupIdBits = 8,

    /// OBI interface
    parameter obi_pkg::obi_cfg_t ObiCfg    = obi_pkg::ObiDefaultConfig,
    parameter type               obi_req_t = logic,
    parameter type               obi_rsp_t = logic,

    /// Dependent parameter, do **not** overwrite.
    parameter type tblock_idx_t = logic [TblockIdxBits-1:0],
    parameter type tgroup_id_t  = logic [ TgroupIdBits-1:0],
    parameter type addr_t       = logic [ AddressWidth-1:0],
    parameter type pc_t         = logic [      PcWidth-1:0]
)(
    // Clock and reset
    input logic clk_i,
    input logic rst_ni,

    // OBI interface
    input  obi_req_t obi_req_i,
    output obi_rsp_t obi_rsp_o,

    // Flush instruction cache
    output logic flush_ic_o,

    // Execute instructions in-order
    output logic inorder_execution_o,

    // Interface to start a new thread block -> to compute clusters
    input  logic        warp_free_i, // The is atleas one free warp that can start a new block
    output logic        allocate_warp_o,
    output pc_t         allocate_pc_o,
    output addr_t       allocate_dp_addr_o, // Data / Parameter address
    output tblock_idx_t allocate_tblock_idx_o, // Block index -> used to calculate the thread id
    output tgroup_id_t  allocate_tgroup_id_o, // Block id -> unique identifier for the block

    // Thread block completion
    output logic       tblock_done_ready_o,
    input  logic       tblock_done_i,
    input  tgroup_id_t tblock_done_id_i
);
    // #######################################################################################
    // # Typedefs                                                                            #
    // #######################################################################################

    typedef logic [ObiCfg.DataWidth-1:0] obi_data_t;
    typedef logic [  ObiCfg.IdWidth-1:0] obi_id_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Request to start dispatching
    logic start_dispatch_q, start_dispatch_d;

    // Are we currently running?
    logic running_q,        running_d;

    // Have we finished?
    logic finished_q,       finished_d;

    // How many thread blocks have finsihed?
    tblock_idx_t finished_tblocks_q, finished_tblocks_d;

    // In-order execution
    logic inorder_execution_q, inorder_execution_d;

    // Configuration
    pc_t         pc_d,                pc_q;
    addr_t       dp_addr_d,           dp_addr_q;
    tblock_idx_t number_of_tblocks_d, number_of_tblocks_q;
    tgroup_id_t  tgroup_id_d,         tgroup_id_q;

    // Obi response signals
    logic      obi_rvalid_q;
    logic      obi_error_q,  obi_error_d;
    obi_data_t obi_rdata_q,  obi_rdata_d;
    obi_id_t   obi_rid_q;

    // Thread Dispatcher ready
    logic        dispatcher_ready;
    tblock_idx_t dispatched_tblocks;

    // #######################################################################################
    // # Combinational Logic                                                                 #
    // #######################################################################################

    // Can only accept done thread blocks if we are running
    assign tblock_done_ready_o = running_q && !start_dispatch_q;

    // Main logic
    always_comb begin : main_logic
        // Default
        start_dispatch_d    = start_dispatch_q;
        running_d           = running_q;
        finished_d          = finished_q;
        finished_tblocks_d  = finished_tblocks_q;
        inorder_execution_d = inorder_execution_q;

        pc_d                = pc_q;
        dp_addr_d           = dp_addr_q;
        number_of_tblocks_d = number_of_tblocks_q;
        tgroup_id_d         = tgroup_id_q;

        obi_error_d  = 1'b0;
        obi_rdata_d  = '0;

        if (obi_req_i.req) begin
            case (obi_req_i.a.addr[5:2])
                'd0: begin : pc_reg
                    if (obi_req_i.a.we) begin
                        if (!running_q)
                            pc_d = obi_req_i.a.wdata[PcWidth-1:0];
                    end else begin
                        obi_rdata_d[PcWidth-1:0] = pc_q;
                    end
                end : pc_reg
                'd1: begin : dp_addr_reg
                    if (obi_req_i.a.we) begin
                        if (!running_q)
                            dp_addr_d = obi_req_i.a.wdata[AddressWidth-1:0];
                    end else begin
                        obi_rdata_d[AddressWidth-1:0] = dp_addr_q;
                    end
                end : dp_addr_reg
                'd2: begin : number_of_tblocks_reg
                    if (obi_req_i.a.we) begin
                        if (!running_q)
                            number_of_tblocks_d = obi_req_i.a.wdata[TblockIdxBits-1:0];
                    end else begin
                        obi_rdata_d[TblockIdxBits-1:0] = number_of_tblocks_q;
                    end
                end : number_of_tblocks_reg
                'd3: begin : tgroup_id_reg
                    if (obi_req_i.a.we) begin
                        if (!running_q)
                            tgroup_id_d = obi_req_i.a.wdata[TgroupIdBits-1:0];
                    end else begin
                        obi_rdata_d[TgroupIdBits-1:0] = tgroup_id_q;
                    end
                end : tgroup_id_reg
                'd4: begin : status_reg
                    if (obi_req_i.a.we) begin
                        if (!running_q) begin
                            // Write to status register triggers a start
                            start_dispatch_d   = 1'b1;
                            running_d          = 1'b1;
                            finished_d         = 1'b0;
                            finished_tblocks_d = '0;

                            // If first bit is set, we execute in-order
                            if (obi_req_i.a.be[0])
                                inorder_execution_d = obi_req_i.a.wdata[0];
                        end
                    end else begin
                        obi_rdata_d[0] = start_dispatch_q;    // Start dispatch
                        obi_rdata_d[1] = running_q;           // Running
                        obi_rdata_d[2] = finished_q;          // Finished
                        obi_rdata_d[3] = inorder_execution_q; // In-order execution
                        obi_rdata_d[TblockIdxBits+3:4] = finished_tblocks_q; // Finished tblocks
                        obi_rdata_d[31:32-TblockIdxBits] = dispatched_tblocks;
                    end
                end : status_reg
                default: begin : obi_error
                    // Default case -> OBI error
                    obi_error_d  = 1'b1;
                end : obi_error
            endcase
        end

        // Dispatch logic, Handshake with the thread dispatcher
        if (start_dispatch_q && dispatcher_ready) begin : dispatch_request
            start_dispatch_d = 1'b0;
        end : dispatch_request

        // A new thread has finished
        if (tblock_done_i && tblock_done_ready_o) begin : tblock_done
            if (tblock_done_id_i == tgroup_id_q) begin
                // Increment finished count
                finished_tblocks_d = finished_tblocks_q + 'd1;

                // If we have finished all thread blocks, we are no longer running
                if (finished_tblocks_d == number_of_tblocks_q) begin
                    running_d  = 1'b0;
                    finished_d = 1'b1;
                end
            end
        end : tblock_done
    end : main_logic

    // Assemble OBI response
    always_comb begin : obi_rsp
        // Default
        obi_rsp_o = '0;

        // We are always ready to accept a new OBI request
        obi_rsp_o.gnt = obi_req_i.req;

        // Build response
        obi_rsp_o.rvalid  = obi_rvalid_q;
        obi_rsp_o.r.rid   = obi_rid_q;
        obi_rsp_o.r.rdata = obi_rdata_q;
        obi_rsp_o.r.err   = obi_error_q;
    end : obi_rsp

    // Flush Instruction Cache when dispatching starts
    assign flush_ic_o = start_dispatch_q && dispatcher_ready;

    // In-order execution
    assign inorder_execution_o = inorder_execution_q;

    // #######################################################################################
    // # Thread Dispatcher                                                                   #
    // #######################################################################################

    thread_dispatcher #(
        .PcWidth      ( PcWidth       ),
        .AddressWidth ( AddressWidth  ),
        .TblockIdxBits( TblockIdxBits ),
        .TgroupIdBits ( TgroupIdBits  )
    ) i_thread_dispatcher (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .ready_o             ( dispatcher_ready    ),
        .start_i             ( start_dispatch_q    ),
        .pc_i                ( pc_q                ),
        .dp_addr_i           ( dp_addr_q           ),
        .number_of_tblocks_i ( number_of_tblocks_q ),
        .tgroup_id_i         ( tgroup_id_q         ),

        .warp_free_i          ( warp_free_i          ),
        .allocate_warp_o      ( allocate_warp_o      ),
        .allocate_pc_o        ( allocate_pc_o        ),
        .allocate_dp_addr_o   ( allocate_dp_addr_o   ),
        .allocate_tblock_idx_o( allocate_tblock_idx_o),
        .allocate_tgroup_id_o ( allocate_tgroup_id_o ),

        .dispatched_tblocks_o( dispatched_tblocks )
    );

    // #######################################################################################
    // # Sequential Logic                                                                    #
    // #######################################################################################

    // Status
    `FF(start_dispatch_q,    start_dispatch_d,    1'b0, clk_i, rst_ni)
    `FF(running_q,           running_d,           1'b0, clk_i, rst_ni)
    `FF(finished_q,          finished_d,          1'b0, clk_i, rst_ni)
    `FF(finished_tblocks_q,  finished_tblocks_d,  '0,   clk_i, rst_ni)
    `FF(inorder_execution_q, inorder_execution_d, 1'b0, clk_i, rst_ni)

    // Configuration
    `FF(pc_q,                pc_d,                '0, clk_i, rst_ni)
    `FF(dp_addr_q,           dp_addr_d,           '0, clk_i, rst_ni)
    `FF(number_of_tblocks_q, number_of_tblocks_d, '0, clk_i, rst_ni)
    `FF(tgroup_id_q,         tgroup_id_d,         '0, clk_i, rst_ni)

    // OBI response
    `FF(obi_rvalid_q, obi_req_i.req,   1'b0, clk_i, rst_ni)
    `FF(obi_error_q,  obi_error_d,     1'b0, clk_i, rst_ni)
    `FF(obi_rdata_q,  obi_rdata_d,     '0,   clk_i, rst_ni)
    `FF(obi_rid_q,    obi_req_i.a.aid, '0,   clk_i, rst_ni)

endmodule : obi_thread_engine
