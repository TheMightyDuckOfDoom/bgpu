// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Compute Unit Instruction Memory Interface to AXI Adapter
module imem_to_axi #(
    // AXI Request and Response Types
    parameter type axi_req_t = logic,
    parameter type axi_rsp_t = logic,

    parameter type axi_addr_t = logic,

    // Instruction Memory Address and Data Types
    parameter type imem_addr_t = logic,
    parameter type imem_data_t = logic
) (
    /// Clock and Reset
    input  logic clk_i,
    input  logic rst_ni,

    /// Instruction Memory Request -> From Compute Unit
    output logic       imem_ready_o,
    input  logic       imem_req_valid_i,
    input  imem_addr_t imem_req_addr_i,

    /// Instruction Memory Response -> To Compute Unit
    output logic       imem_rsp_valid_o,
    output imem_data_t imem_rsp_data_o,

    /// AXI Request -> To Memory
    output axi_req_t   axi_req_o,

    /// AXI Response -> From Memory
    input  axi_rsp_t   axi_rsp_i
);

    // #######################################################################################
    // # Local Parameters                                                                    #
    // #######################################################################################

    localparam axi_pkg::size_t AxiSize = axi_pkg::size_t'($unsigned($clog2($bits(imem_data_t)/8)));

    // #######################################################################################
    // # Request                                                                             #
    // #######################################################################################

    assign imem_ready_o = axi_rsp_i.ar_ready;

    assign axi_req_o = '{
        ar_valid: imem_req_valid_i,
        ar: '{
            // Convert to byte address
            addr:  axi_addr_t'(imem_req_addr_i) << ($clog2($bits(imem_data_t)/8)),
            prot:  '0,
            size:  AxiSize,
            burst: axi_pkg::BURST_FIXED,
            cache: axi_pkg::CACHE_BUFFERABLE | axi_pkg::CACHE_MODIFIABLE,
            default: '0
        },
        // Always ready to receive read data
        r_ready:  1'b1,
        // No write requests
        default:   '0
    };

    // #######################################################################################
    // # Response                                                                            #
    // #######################################################################################

    assign imem_rsp_valid_o  = axi_rsp_i.r_valid;
    assign imem_rsp_data_o   = axi_rsp_i.r.data;

    // #######################################################################################
    // # Assertions                                                                          #
    // #######################################################################################

    `ifndef SYNTHESIS
        assert property (@(posedge clk_i) disable iff (!rst_ni)
            axi_rsp_i.r_valid |-> axi_rsp_i.r.resp == axi_pkg::RESP_OKAY)
            else $error("AXI Response is not OKAY, but valid. Response: %0h", axi_rsp_i.r.resp);
    `endif
endmodule : imem_to_axi
