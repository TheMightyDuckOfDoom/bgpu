// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "common_cells/registers.svh"
`include "bgpu/instructions.svh"

/// Load Store Unit
// Performs load and store operations
// Requests are coalesced into a minimum number of blocks and sent to the memory interface
// in the order that they were received by the Load Store Unit.
// This means that memory ordering has to be checked/enforced by another mechanism.
// Memory responses can be received in any order, but must have atleas one cycle of latency
// Operand 0 is the address for load/store operations
module load_store_unit #(
    // Width of the registers
    parameter int unsigned RegWidth = 32,
    // Number of threads in a warp
    parameter int unsigned WarpWidth = 4,
    // Number of operands per instruction
    parameter int unsigned OperandsPerInst = 2,
    // How many registers can each warp access as operand or destination
    parameter int unsigned RegIdxWidth = 8,
    // Tag data type
    parameter type iid_t = logic,

    // Memory Address width in bits
    parameter int unsigned AddressWidth = 32,
    // Memory Block size in bytes -> Memory request width
    parameter int unsigned BlockIdxBits = 4,
    // Width of the id for requests queue
    parameter int unsigned OutstandingReqIdxWidth = 3,

    /// Dependent parameter, do **not** overwrite.
    parameter int unsigned BlockWidth      = 1 << BlockIdxBits, // In bytes
    parameter int unsigned BlockAddrWidth  = AddressWidth - BlockIdxBits,
    parameter int unsigned OutstandingReqs = 1 << OutstandingReqIdxWidth,
    parameter int unsigned ThreadIdxWidth  = WarpWidth > 1 ? $clog2(WarpWidth) : 1,
    parameter type warp_data_t  = logic  [RegWidth * WarpWidth-1:0],
    parameter type reg_idx_t    = logic  [         RegIdxWidth-1:0],
    parameter type block_addr_t = logic  [      BlockAddrWidth-1:0],
    parameter type byte_t       = logic  [                     7:0],
    parameter type block_data_t = byte_t [          BlockWidth-1:0],
    parameter type block_idx_t  = logic  [        BlockIdxBits-1:0],
    parameter type block_mask_t = logic  [          BlockWidth-1:0],
    parameter type act_mask_t   = logic  [           WarpWidth-1:0],
    parameter type req_id_t     = logic  [OutstandingReqIdxWidth + ThreadIdxWidth-1:0]
) (
    /// Clock and Reset
    input logic clk_i,
    input logic rst_ni,

    /// Memory Request
    input  logic        mem_ready_i,
    output logic        mem_req_valid_o,
    output req_id_t     mem_req_id_o,
    output block_addr_t mem_req_addr_o,
    output block_mask_t mem_req_we_mask_o,

    /// Memory Response
    input  logic        mem_rsp_valid_i,
    input  req_id_t     mem_rsp_id_i,
    input  block_data_t mem_rsp_data_i,

    /// From Operand Collector
    output logic               eu_to_opc_ready_o,
    input  logic               opc_to_eu_valid_i,
    input  iid_t               opc_to_eu_tag_i,
    input  act_mask_t          opc_to_eu_act_mask_i,
    input  bgpu_inst_subtype_e opc_to_eu_inst_sub_i,
    input  reg_idx_t           opc_to_eu_dst_i,
    input  warp_data_t         [OperandsPerInst-1:0] opc_to_eu_operands_i,

    // To Result Collector
    input  logic       rc_to_eu_ready_i,
    output logic       eu_to_rc_valid_o,
    output iid_t       eu_to_rc_tag_o,
    output reg_idx_t   eu_to_rc_dst_o,
    output warp_data_t eu_to_rc_data_o
);
    // #######################################################################################
    // # Type Definitions                                                                    #
    // #######################################################################################

    typedef logic       [AddressWidth-1:0] addr_t;
    typedef addr_t      [   WarpWidth-1:0] req_addr_t;
    typedef block_idx_t [   WarpWidth-1:0] offsets_t;

    typedef logic       [OutstandingReqIdxWidth-1:0] com_req_id_t;
    typedef logic       [             WarpWidth-1:0] sub_req_id_t;

    // Data passed from the Coalesce Splitter to the Wdata Assembler
    typedef struct packed {
        com_req_id_t com_id;
        sub_req_id_t sub_id;
        block_addr_t addr;
        warp_data_t  wdata;
        block_mask_t we_mask;
        block_idx_t [WarpWidth-1:0] offsets;
    } coalesce_splitter_to_wdata_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // New instruction is a write
    logic opc_to_eu_is_write;
    // Operand 0 truncated to address width
    req_addr_t opc_to_eu_addr;

    logic cs_to_wdata_valid_d, cs_to_wdata_valid_q;
    logic wdata_to_cs_ready_d, wdata_to_cs_ready_q;
    act_mask_t cs_to_wdata_valid_mask;
    coalesce_splitter_to_wdata_t cs_to_wdata_d, cs_to_wdata_q;

    // #######################################################################################
    // # Combinational logic                                                                 #
    // #######################################################################################

    // #######################################################################################
    // # Coalesce Splitter                                                                   #
    // #######################################################################################

    // Operand 0 is the address for load/store operations
    // Truncate to address width
    for(genvar i = 0; i < WarpWidth; i++) begin : gen_addr
        assign opc_to_eu_addr[i] = opc_to_eu_operands_i[0][i*RegWidth +: AddressWidth];
    end : gen_addr
    
    // Check if the instruction is a write
    assign opc_to_eu_is_write = opc_to_eu_inst_sub_i == BGPU_INST_SUBTYPE_STORE;

    coalesce_splitter #(
        .NumRequests ( WarpWidth    ),
        .AddressWidth( AddressWidth ),
        .BlockIdxBits( BlockIdxBits )
    ) i_coalesce_splitter (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .ready_o      ( eu_to_opc_ready_o    ),
        .valid_i      ( opc_to_eu_valid_i    ),
        .we_i         ( opc_to_eu_is_write   ),
        .addr_valid_i ( opc_to_eu_act_mask_i ),
        .addr_i       ( opc_to_eu_addr       ),

        .req_ready_i  ( wdata_to_cs_ready_q   ),
        .req_valid_o  ( cs_to_wdata_valid_d   ),
        .req_we_o     ( cs_to_wdata_d.we_mask ),
        .req_com_id_o ( cs_to_wdata_d.com_id  ),
        .req_sub_id_o ( cs_to_wdata_d.sub_id  ),
        .req_addr_o   ( cs_to_wdata_d.addr    ),
        .req_offsets_o( cs_to_wdata_d.offsets )
    );

    // #######################################################################################
    // # Register between Coalesce Splitter and Wdata Assembler                              #
    // #######################################################################################

    stream_register #(
        .T( coalesce_splitter_to_wdata_t )
    ) i_cs_to_wdata_reg (
        .clk_i ( clk_i ),
        .rst_ni( rst_ni ),

        .valid_i( cs_to_wdata_valid_d ),
        .ready_o( wdata_to_cs_ready_q ),
        .data_i ( cs_to_wdata_d       ),

        .valid_o( cs_to_wdata_valid_q ),
        .ready_i( wdata_to_cs_ready_d ),
        .data_o ( cs_to_wdata_q       )
    );

    // #######################################################################################
    // # Sequential logic                                                                    #
    // #######################################################################################

    // #######################################################################################
    // # Assertions                                                                          #
    // #######################################################################################

endmodule : load_store_unit
