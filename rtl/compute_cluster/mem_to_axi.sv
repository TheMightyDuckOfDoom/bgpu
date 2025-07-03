// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Compute Unit Memory Interface to AXI Adapter
module mem_to_axi #(
    // AXI Request and Response Types
    parameter type axi_req_t = logic,
    parameter type axi_rsp_t = logic,

    parameter type axi_addr_t = logic,

    parameter type req_id_t     = logic,
    parameter type block_addr_t = logic,
    parameter type block_mask_t = logic,
    parameter type block_data_t = logic
) (
    /// Clock and Reset
    input  logic clk_i,
    input  logic rst_ni,

    /// Memory Request -> From Compute Unit
    output logic        mem_ready_o,
    input  logic        mem_req_valid_i,
    input  req_id_t     mem_req_id_i,
    input  block_addr_t mem_req_addr_i,
    input  block_mask_t mem_req_we_mask_i,
    input  block_data_t mem_req_wdata_i,

    /// Memory Response -> To Compute Unit
    output logic        mem_rsp_valid_o,
    output req_id_t     mem_rsp_id_o,
    output block_data_t mem_rsp_data_o,

    /// AXI Request -> To Memory
    output axi_req_t   axi_req_o,

    /// AXI Response -> From Memory
    input  axi_rsp_t   axi_rsp_i
);

    // #######################################################################################
    // # Local Parameters                                                                    #
    // #######################################################################################

    localparam axi_pkg::size_t AxiSize = axi_pkg::size_t'($unsigned($clog2($bits(block_data_t)/8)));

    // Memory Response to Compute Unit
    typedef struct packed {
        req_id_t     id;
        block_data_t data;
    } rsp_t;

    // #######################################################################################
    // # Request -> Demux(AR ,Fork(AW, W)) channels                                            #
    // #######################################################################################

    logic aww_valid, aww_ready;

    // Demux into AR or AW/W channels
    stream_demux #(
        .N_OUP( 2 )
    ) i_ar_aww_demux (
        .inp_valid_i( mem_req_valid_i ),
        .inp_ready_o( mem_ready_o     ),

        // 0 -> Read (AR), 1 -> Write (AW/W)
        .oup_sel_i( mem_req_we_mask_i != '0 ),

        .oup_valid_o( { aww_valid, axi_req_o.ar_valid } ),
        .oup_ready_i( { aww_ready, axi_rsp_i.ar_ready } )
    );

    // Fork the AW and W channels
    stream_fork #(
        .N_OUP( 2 )
    ) i_aw_w_fork (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .valid_i( aww_valid ),
        .ready_o( aww_ready ),

        .valid_o( { axi_req_o.aw_valid, axi_req_o.w_valid } ),
        .ready_i( { axi_rsp_i.aw_ready, axi_rsp_i.w_ready } )
    );

    // AR channel request
    assign axi_req_o.ar = '{
        // Convert to byte address
        addr:    axi_addr_t'(mem_req_addr_i) << ($clog2($bits(block_data_t)/8)),
        id:      mem_req_id_i,
        prot:    '0,
        size:    AxiSize,
        burst:   axi_pkg::BURST_FIXED,
        cache:   axi_pkg::CACHE_BUFFERABLE | axi_pkg::CACHE_MODIFIABLE,
        default: '0
    };

    // AW channel request
    assign axi_req_o.aw = '{
        // Convert to byte address
        addr:    axi_addr_t'(mem_req_addr_i) << ($clog2($bits(block_data_t)/8)),
        id:      mem_req_id_i,
        prot:    '0,
        size:    AxiSize,
        burst:   axi_pkg::BURST_FIXED,
        cache:   axi_pkg::CACHE_BUFFERABLE | axi_pkg::CACHE_MODIFIABLE,
        default: '0
    };

    // W channel request
    assign axi_req_o.w = '{
        data:    mem_req_wdata_i,
        strb:    mem_req_we_mask_i,
        // Always last
        last:    1'b1,
        default: '0
    };

    // #######################################################################################
    // # Response -> Arbitrate between B and R channels                                      #
    // #######################################################################################

    // Memory Responses
    rsp_t b_rsp, r_rsp, mem_rsp;

    // B channel response
    assign b_rsp.id = axi_rsp_i.b.id;
    // Write responses do not carry data
    assign b_rsp.data = '0;

    // R channel response
    assign r_rsp.id   = axi_rsp_i.r.id;
    assign r_rsp.data = axi_rsp_i.r.data;

    // Arbitrate B and R responses
    stream_arbiter #(
        .DATA_T ( rsp_t ),
        .N_INP  ( 2     ),
        .ARBITER( "rr"  )
    ) i_rsp_arbiter (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .inp_data_i ( { b_rsp, r_rsp } ),
        .inp_valid_i( { axi_rsp_i.b_valid, axi_rsp_i.r_valid } ),
        .inp_ready_o( { axi_req_o.b_ready, axi_req_o.r_ready } ),

        .oup_data_o ( mem_rsp         ),
        .oup_valid_o( mem_rsp_valid_o ),
        // Compute Unit is always ready for responses
        .oup_ready_i( 1'b1            )
    );

    // Extract memory response
    assign mem_rsp_id_o   = mem_rsp.id;
    assign mem_rsp_data_o = mem_rsp.data;

endmodule : mem_to_axi
