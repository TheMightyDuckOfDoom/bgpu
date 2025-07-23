// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "common_cells/registers.svh"

/// Single register file bank
module register_file_bank #(
    /// Number of threads per warp
    parameter int unsigned WarpWidth = 8,
    /// Width of a single register
    parameter int unsigned RegisterWidth = 32,
    /// Number of registers
    parameter int unsigned NumRegisters = 32,
    /// Should the memory be a dual port memory?
    parameter bit DualPort = 1'b0,
    /// Tag that identifies a read request
    parameter type tag_t = logic,

    /// Dependent parameter, do **not** overwrite.
    parameter type addr_t      = logic  [$clog2(NumRegisters)-1:0],
    parameter type data_t      = logic  [RegisterWidth-1:0],
    parameter type warp_data_t = data_t [WarpWidth-1:0],
    parameter type we_mask_t   = logic  [WarpWidth-1:0]
) (
    /// Clock and reset
    input logic clk_i,
    input logic rst_ni,

    /// Write port
    input  logic       write_valid_i,
    input  we_mask_t   write_mask_i,
    input  addr_t      write_addr_i,
    input  warp_data_t write_data_i,
    output logic       write_ready_o,

    /// Read port
    input  logic  read_valid_i,
    output logic  read_ready_o,
    input  addr_t read_addr_i,
    input  tag_t  read_tag_i,

    /// Read output
    output logic       read_valid_o,
    output tag_t       read_tag_o,
    output warp_data_t read_data_o
);
    // #######################################################################################
    // # Local Parameters                                                                    #
    // #######################################################################################

    localparam int unsigned NumPorts         = DualPort ? 2 : 1;
    localparam int unsigned BytesPerRegister = RegisterWidth / 8;
    localparam int unsigned BeWidth          = BytesPerRegister * WarpWidth;

    // #######################################################################################
    // # Type Definitions                                                                    #
    // #######################################################################################

    typedef logic [BeWidth-1:0] be_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Memory request signals
    logic       [NumPorts-1:0] mem_req;
    logic       [NumPorts-1:0] mem_we;
    addr_t      [NumPorts-1:0] mem_addr;
    warp_data_t [NumPorts-1:0] mem_wdata;
    warp_data_t [NumPorts-1:0] mem_rdata;
    be_t        [NumPorts-1:0] mem_be;

    // Do we have a valid read |-> output in next cycle?
    logic read_valid_d;

    // Write mask as byte enable
    be_t write_mask_be;

    // #######################################################################################
    // # Combinational logic                                                                 #
    // #######################################################################################

    // Build byte enable from write mask
    for (genvar warp = 0; warp < WarpWidth; warp++) begin : gen_write_mask_be
        always_comb begin : warp_write_mask_be
            write_mask_be[(warp * BytesPerRegister) +: BytesPerRegister] = '0;

            if (write_mask_i[warp]) begin
                // Set byte enable for this warp
                write_mask_be[(warp * BytesPerRegister) +: BytesPerRegister] = '1;
            end
        end : warp_write_mask_be
    end : gen_write_mask_be

    if (DualPort) begin : gen_dual_port_logic
        // Port 0: Read port
        assign mem_req  [0] = read_valid_i;
        assign mem_addr [0] = read_addr_i;
        assign mem_wdata[0] = '0;
        assign mem_we   [0] = 1'b0;
        assign mem_be   [0] = '1;
        assign read_ready_o = 1'b1;
        assign read_valid_d = read_valid_i;

        // Port 1: Write port
        assign mem_req  [1]  = write_valid_i;
        assign mem_addr [1]  = write_addr_i;
        assign mem_wdata[1]  = write_data_i;
        assign mem_we   [1]  = 1'b1;
        assign mem_be   [1]  = write_mask_be;
        assign write_ready_o = 1'b1;
    end : gen_dual_port_logic
    else begin : gen_single_port_logic
        // Currently writes have priority over reads
        always_comb begin
            // Default values
            mem_req   = '0;
            mem_we    = '0;
            mem_addr  = '0;
            mem_wdata = '0;
            mem_be    = '0;

            // By default, both ports are ready
            read_ready_o  = 1'b1;
            write_ready_o = 1'b1;

            // We have not started a read yet
            read_valid_d = 1'b0;

            // Write has priority over read
            if (write_valid_i) begin
                // Write request
                mem_req  [0] = 1'b1;
                mem_we   [0] = 1'b1;
                mem_addr [0] = write_addr_i;
                mem_wdata[0] = write_data_i;
                mem_be   [0] = write_mask_be;

                // Read is not ready
                read_ready_o = 1'b0;
            end else if (read_valid_i) begin
                // Read request
                mem_req  [0] = 1'b1;
                mem_we   [0] = 1'b0;
                mem_addr [0] = read_addr_i;
                mem_be   [0] = '1;
                read_valid_d = 1'b1;

                // Write is not ready
                write_ready_o = 1'b0;
            end
        end
    end : gen_single_port_logic

    // Read data comes one cycle later from the memory
    assign read_data_o = mem_rdata[0];

    // #######################################################################################
    // # Sequential logic                                                                    #
    // #######################################################################################

    // Delay read valid and tag by one cycle
    `FF(read_valid_o, read_valid_d, '0, clk_i, rst_ni);
    `FF(read_tag_o,   read_tag_i,   '0, clk_i, rst_ni);

    // #######################################################################################
    // # Memory                                                                              #
    // #######################################################################################

    tc_sram #(
        .NumWords   ( NumRegisters              ),
        .DataWidth  ( WarpWidth * RegisterWidth ),
        .ByteWidth  ( 8                         ),
        .NumPorts   ( NumPorts                  ),
        .Latency    ( 1                         ),
        .SimInit    ( "ones"                    ),
        .PrintSimCfg( 1'b1                      ),
        .ImplKey    ( "register_file_bank"      )
    ) i_tc_sram (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .req_i  ( mem_req   ),
        .we_i   ( mem_we    ),
        .addr_i ( mem_addr  ),
        .wdata_i( mem_wdata ),
        .be_i   ( mem_be    ),
        .rdata_o( mem_rdata )
    );

    // #######################################################################################
    // # Assertions                                                                          #
    // #######################################################################################

    `ifndef SYNTHESIS
        initial assert(NumPorts == 1 || NumPorts == 2)
            else $error("Number of ports must be 1 or 2!");

        initial assert(WarpWidth > 0)
            else $error("Warp width must be greater than 0!");

        initial assert(RegisterWidth > 0 && RegisterWidth % 8 == 0)
            else $error("Register width must be a multiple of 8!");
    `endif

endmodule : register_file_bank
