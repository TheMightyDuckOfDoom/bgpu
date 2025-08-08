// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "axi/typedef.svh"

/// Converts an AXI bus to a GOWIN / Xilinx DDR3 Memory controller interface.
module axi_to_mctrl #(
    /// Width of the data bus to the memory controller
    parameter int unsigned MctrlWidth = 64,
    /// Width of the addressable physical memory by the memory controller
    parameter int unsigned MctrlAddressWidth = 24,
    /// Width of the AXI ID bus to the memory controller
    parameter int unsigned MctrlAxiIdWidth = 8,

    /// Number of pending requests
    parameter int unsigned MaxPendingRequests = 8,

    /// AXI Types
    parameter type axi_req_t  = logic,
    parameter type axi_resp_t = logic,

    /// Dependent parameter, do **not** overwrite.
    parameter type mctrl_addr_t = logic [MctrlAddressWidth-1:0],
    parameter type mctrl_mask_t = logic [     MctrlWidth/8-1:0],
    parameter type mctrl_data_t = logic [       MctrlWidth-1:0]
) (
    /// Clock and Reset
    input logic clk_i,
    input logic rst_ni,

    // Testmode
    input logic testmode_i,

    /// AXI Interface
    input  axi_req_t  axi_req_i,
    output axi_resp_t axi_rsp_o,

    /// Memory Controller Interface
    // Command
    input  logic        mctrl_cmd_ready_i,
    output logic        mctrl_cmd_valid_o,
    output logic        mctrl_cmd_read_o,
    output mctrl_addr_t mctrl_cmd_addr_o,

    // Write
    input  logic        mctrl_wdata_ready_i,
    output logic        mctrl_wdata_valid_o,
    output mctrl_data_t mctrl_wdata_o,
    output mctrl_mask_t mctrl_wmask_o,

    // Read
    input logic        mctrl_rdata_valid_i,
    input mctrl_data_t mctrl_rdata_i
);
    // #######################################################################################
    // # Type Definitions                                                                    #
    // #######################################################################################

    typedef struct packed {
        logic        we;
        mctrl_addr_t addr;
        mctrl_data_t wdata;
        mctrl_mask_t wmask;
    } mem_req_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Memory Request / Response signals in clk_i domain
    logic     mem_req_valid, mem_req_ready;
    mem_req_t mem_req;

    logic        mem_rsp_valid;
    mctrl_data_t mem_rsp_rdata;

    // Write Data Fork
    logic wdata_fork_valid;

    // Cmd fifo
    logic fifo_in_valid,  fifo_in_ready;
    logic fifo_out_valid, fifo_out_ready, fifo_out_write;

    // #######################################################################################
    // # AXI2Memory                                                                          #
    // #######################################################################################

    axi_to_mem #(
        .axi_req_t   ( axi_req_t          ),
        .axi_resp_t  ( axi_resp_t         ),
        .AddrWidth   ( MctrlAddressWidth  ),
        .DataWidth   ( MctrlWidth         ),
        .IdWidth     ( MctrlAxiIdWidth    ),
        .NumBanks    ( 1                  ),
        .BufDepth    ( MaxPendingRequests ),
        .HideStrb    ( 1'b0               ), /// This currently is buggy when enabled
        .OutFifoDepth( 1                  )
    ) i_axi_to_mem (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .axi_req_i ( axi_req_i ),
        .axi_resp_o( axi_rsp_o ),

        .mem_req_o  ( mem_req_valid ),
        .mem_gnt_i  ( mem_req_ready ),
        .mem_addr_o ( mem_req.addr  ),
        .mem_we_o   ( mem_req.we    ),
        .mem_wdata_o( mem_req.wdata ),
        .mem_strb_o ( mem_req.wmask ),

        .mem_rvalid_i( mem_rsp_valid ),
        .mem_rdata_i ( mem_rsp_rdata ),

        .busy_o    ( /* Unused */ ),
        .mem_atop_o( /* Unused */ )
    );

    // #######################################################################################
    // # Memory Controller Interface                                                         #
    // #######################################################################################

    // Command
    assign mctrl_cmd_read_o = !mem_req.we;
    assign mctrl_cmd_addr_o = mem_req.addr;

    // Fork between command, write data and cmd response fifo
    stream_fork #(
        .N_OUP( 3 )
    ) i_stream_fork (
        .clk_i  ( clk_i         ),
        .rst_ni ( rst_ni        ),
        .valid_i( mem_req_valid ),
        .ready_o( mem_req_ready ),

        .valid_o( {mctrl_cmd_valid_o, wdata_fork_valid,    fifo_in_valid} ),
        .ready_i( {mctrl_cmd_ready_i, mctrl_wdata_ready_i, fifo_in_ready} )
    );

    // CMD type fifo: 1 write, 0 read
    stream_fifo #(
        .FALL_THROUGH ( 1'b0               ),
        .DEPTH        ( MaxPendingRequests ),
        .DATA_WIDTH   ( 1                  )
    ) i_cmd_fifo (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .flush_i   ( 1'b0         ),
        .testmode_i( testmode_i   ),
        .usage_o   ( /* Unused */ ),

        .data_i ( mem_req.we      ),
        .valid_i( fifo_in_valid   ),
        .ready_o( fifo_in_ready   ),

        .data_o ( fifo_out_write  ),
        .valid_o( fifo_out_valid  ),
        .ready_i( fifo_out_ready  )
    );

    // Write
    assign mctrl_wdata_o       = mem_req.wdata;
    assign mctrl_wmask_o       = mem_req.wmask;
    assign mctrl_wdata_valid_o = wdata_fork_valid && mem_req.we;

    // Response for Writes and Reads
    assign mem_rsp_rdata = mctrl_rdata_i;
    assign fifo_out_ready = mem_rsp_valid;

    always_comb begin
        mem_rsp_valid = mctrl_rdata_valid_i;

        // If a write is in the fifo, then we can send out a response,
        // if we are not already sending one.
        if ((!mem_rsp_valid) && fifo_out_valid && fifo_out_write) begin
            mem_rsp_valid = 1'b1;
        end
    end

endmodule : axi_to_mctrl
