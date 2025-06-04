// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "common_cells/registers.svh"
`include "bgpu/instructions.svh"

/// Load Store Unit
// Performs load and store operations
// Requests are coalesced into a minimum number of blocks and sent to the memory interface in-order
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
    parameter type block_mask_t = logic  [          BlockWidth-1:0],
    parameter type block_addr_t = logic  [      BlockAddrWidth-1:0],
    parameter type byte_t       = logic  [                     7:0],
    parameter type block_data_t = byte_t [          BlockWidth-1:0],
    parameter type block_idx_t  = logic  [        BlockIdxBits-1:0],
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
    output act_mask_t   mem_req_we_o,
    output block_idx_t  [WarpWidth-1:0] mem_req_write_idx_o,
    output warp_data_t  mem_req_wdata_o,

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

    typedef logic [ThreadIdxWidth-1:0] req_num_t;

    typedef logic [RegWidth-1:0] reg_data_t;

    typedef struct packed {
        logic     is_load;
        iid_t     tag;
        reg_idx_t dst;
        logic       [WarpWidth-1:0] request_sent;
        logic       [WarpWidth-1:0] data_received;
        req_num_t   [WarpWidth-1:0] req_num;
        block_idx_t [WarpWidth-1:0] block_idx;
        warp_data_t data;
    } request_entry_t;

    typedef logic [AddressWidth-1:0] addr_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Coalescing info -> keeps track if we still have requests pending or not
    req_id_t   coalesce_req_id_q, coalesce_req_id_d, coalesce_req_id;
    // Pending threads for the current request -> still need to requests from memory
    act_mask_t opc_to_eu_act_mask_q, opc_to_eu_act_mask_d, opc_to_eu_act_mask;
    
    warp_data_t opc_to_eu_operand_0;
    addr_t [WarpWidth-1:0] opc_to_eu_operands_addr, opc_to_eu_operands_addr_q, opc_to_eu_operands_addr_d;

    // Output from Coalescing Comparator
    block_addr_t coalesced_addr;                          // Address of the coalesced block
    // Which threads are part of the coalesced request
    act_mask_t   coalesced_members;
    // Offsets of each thread relative to the coalesced address
    block_idx_t  [WarpWidth-1:0] coalesced_block_offsets;

    // Request queue
    logic           [OutstandingReqs-1:0] req_queue_valid_q, req_queue_valid_d;
    request_entry_t [OutstandingReqs-1:0] req_queue_q,       req_queue_d;

    // Current active request entry
    logic [OutstandingReqIdxWidth-1:0] mem_req_idx;

    logic [BlockWidth + RegWidth / 8:0] mem_req_we; // Memory write enable for each byte in the block

    // Request entry selected by memory response
    logic [OutstandingReqIdxWidth-1:0] mem_rsp_idx;
    request_entry_t mem_rsp_req_entry;

    // Extended memory response data
    logic [BlockWidth * 8 + RegWidth - 1:0] mem_rsp_rdata_ext;

    // #######################################################################################
    // # Combinational logic                                                                 #
    // #######################################################################################

    // We are ready if there is space in the request queue
    // Memory is ready to accept a new request and we have no pending requests
    assign eu_to_opc_ready_o = !(&req_queue_valid_q) && mem_ready_i && !(|opc_to_eu_act_mask_q);

    // Current active request entry that is sent to memory
    assign mem_req_idx = mem_req_id_o[OutstandingReqIdxWidth+ThreadIdxWidth-1:ThreadIdxWidth];

    // Select the request entry using memory reponse id
    assign mem_rsp_idx       = mem_rsp_id_i[OutstandingReqIdxWidth+ThreadIdxWidth-1:ThreadIdxWidth];
    assign mem_rsp_req_entry = req_queue_q[mem_rsp_idx];

    // Extend the memory response data, as we could select the last byte of the block
    assign mem_rsp_rdata_ext = { {RegWidth{1'b0}}, mem_rsp_data_i };

    always_comb begin : comb_logic
        // Default
        req_queue_valid_d          = req_queue_valid_q;
        req_queue_d                = req_queue_q;

        eu_to_rc_valid_o = 1'b0;
        eu_to_rc_tag_o   = '0;
        eu_to_rc_dst_o   = '0;
        eu_to_rc_data_o  = '0;

        mem_req_valid_o     = 1'b0;
        mem_req_we_o        = '0;
        mem_req_write_idx_o = '0;
        mem_req_wdata_o     = '0;

        coalesce_req_id = coalesce_req_id_q;

        // Insert handshake
        if (opc_to_eu_valid_i && eu_to_opc_ready_o) begin : insert
            // Find first free entry and insert it
            for (int i = 0; i < OutstandingReqs; i++) begin
                if (!req_queue_valid_q[i]) begin
                    // We start a new request
                    coalesce_req_id = '0; // First request of this entry
                    coalesce_req_id[OutstandingReqIdxWidth+ThreadIdxWidth-1:ThreadIdxWidth]
                        = i[OutstandingReqIdxWidth-1:0];
                    req_queue_valid_d[i]         = 1'b1;
                    req_queue_d[i].is_load       = (opc_to_eu_inst_sub_i == LSU_LOAD);
                    req_queue_d[i].tag           = opc_to_eu_tag_i;
                    req_queue_d[i].dst           = opc_to_eu_dst_i;
                    req_queue_d[i].request_sent  = coalesced_members;
                    req_queue_d[i].req_num       = '0; // First request for this entry
                    req_queue_d[i].data_received = ~opc_to_eu_act_mask_i; // Threads that are inactive are already received
                    // Contains all block offsets, even those that are not part of the current request
                    req_queue_d[i].block_idx     = coalesced_block_offsets;
                    req_queue_d[i].data          = req_queue_d[i].is_load ? '0 : opc_to_eu_operands_i[1]; // Store operand 1 for write requests

                    // Send the first request
                    mem_req_valid_o = 1'b1;

                    // Build write request
                    mem_req_we_o        = req_queue_d[i].is_load ? '0 : coalesced_members;
                    mem_req_write_idx_o = coalesced_block_offsets;
                    mem_req_wdata_o     = opc_to_eu_operands_i[1];

                    break;
                end
            end
        end : insert

        // If we still have pending requests, we send it and update the request mask
        if(|opc_to_eu_act_mask_q) begin
            mem_req_valid_o = 1'b1;

            // // Build write request
            mem_req_we_o        = req_queue_q[mem_req_idx].is_load ? '0 : coalesced_members;
            mem_req_write_idx_o = coalesced_block_offsets;
            mem_req_wdata_o     = req_queue_q[mem_req_idx].data;

            // Request is sent to memory, mark them as sent and update their request number
            if (mem_ready_i) begin
                req_queue_d[mem_req_idx].request_sent
                    = req_queue_d[mem_req_idx].request_sent | coalesced_members;
                for(int i = 0; i < WarpWidth; i++) begin
                    if (coalesced_members[i]) begin
                        req_queue_d[mem_req_idx].req_num[i] = coalesce_req_id[ThreadIdxWidth-1:0];
                    end
                end
            end
        end

        // Receive memory response
        if(mem_rsp_valid_i) begin : handle_mem_rsp
            if (mem_rsp_req_entry.is_load) begin : handle_load_rsp
                for(int i = 0; i < WarpWidth; i++) begin
                    // Check if the thread still requires the data, and the response is for this thread
                    if (mem_rsp_req_entry.request_sent[i] && !mem_rsp_req_entry.data_received[i]
                            && mem_rsp_req_entry.req_num[i] == mem_rsp_id_i[ThreadIdxWidth-1:0]) begin
                        // We have received the data for this thread
                        req_queue_d[mem_rsp_idx].data_received[i] = 1'b1;

                        // Store the data in the request entry
                        req_queue_d[mem_rsp_idx].data[i * RegWidth +: RegWidth]
                            = mem_rsp_rdata_ext[mem_rsp_req_entry.block_idx[i] * 8 +: RegWidth];
                    end
                end
            end : handle_load_rsp
            else begin : handle_store_rsp
                // Mark all threads as having received the data if we get a store response
                req_queue_d[mem_rsp_idx].data_received = '1;
            end
        end : handle_mem_rsp
    
        // Find first request that has received all data
        for(int i = 0; i < OutstandingReqs; i++) begin
            // If the request is valid and all threads have received the data
            if (req_queue_valid_q[i] && (&req_queue_q[i].data_received)) begin
                // We can send the result to the result collector
                eu_to_rc_valid_o = 1'b1;
                eu_to_rc_tag_o   = req_queue_q[i].tag;
                eu_to_rc_dst_o   = req_queue_q[i].dst;
                eu_to_rc_data_o = req_queue_q[i].data;

                // Remove the request from the queue if we have an output handshake
                if(rc_to_eu_ready_i) begin
                    req_queue_valid_d[i] = 1'b0;
                end

                break; // We can stop here, as we only send one response at a time
            end
        end
    end : comb_logic

    // Truncate first operand to address width
    assign opc_to_eu_operand_0 = opc_to_eu_operands_i[0];
    for(genvar i = 0; i < WarpWidth; i++) begin : gen_truncate_address
        assign opc_to_eu_operands_addr[i]
            = opc_to_eu_operand_0[i * RegWidth +: RegWidth];
    end : gen_truncate_address

    // Update coalescing info if we make a new request
    // Otherwise keep the previous info -> Might have to still process the previous request
    assign opc_to_eu_operands_addr_d = (opc_to_eu_valid_i && eu_to_opc_ready_o)
        ? opc_to_eu_operands_addr
        : opc_to_eu_operands_addr_q;

    assign opc_to_eu_act_mask = (opc_to_eu_valid_i && eu_to_opc_ready_o
        ? opc_to_eu_act_mask_i // New request -> Want to coalesce all threads
        : opc_to_eu_act_mask_q);

    // If we have a request handshake -> we can remove the member from the coalescing info
    assign opc_to_eu_act_mask_d = (mem_req_valid_o && mem_ready_i)
        ? opc_to_eu_act_mask & ~coalesced_members // Remove threads that are part of the request
        : opc_to_eu_act_mask_q; // Keep the previous info

    // If we have made a memory request, we can increment the request number
    always_comb begin : increment_req_num
        // Default
        coalesce_req_id_d = coalesce_req_id;

        // Increment request number for the current request
        if (mem_req_valid_o && mem_ready_i) begin
            coalesce_req_id_d[ThreadIdxWidth-1:0] = coalesce_req_id[ThreadIdxWidth-1:0] + 'd1;
        end
    end : increment_req_num

    // Build memory request
    assign mem_req_id_o   = coalesce_req_id;
    assign mem_req_addr_o = coalesced_addr;

    // #######################################################################################
    // # Coalesce Comparator                                                                 #
    // #######################################################################################

    coalesce_comparator #(
        .AddressWidth( AddressWidth ),
        .NumRequests ( WarpWidth    ),
        .BlockIdxBits( BlockIdxBits )
    ) i_coalesce_comparator (
        .req_valid_i( opc_to_eu_act_mask        ),
        .req_addr_i ( opc_to_eu_operands_addr_d ),

        .coalesced_addr_o      ( coalesced_addr          ),
        .members_o             ( coalesced_members       ),
        .member_block_offsets_o( coalesced_block_offsets )
    );

    // #######################################################################################
    // # Sequential logic                                                                    #
    // #######################################################################################

    // Coalescing info
    `FF(coalesce_req_id_q,         coalesce_req_id_d,         '0, clk_i, rst_ni);
    `FF(opc_to_eu_act_mask_q,      opc_to_eu_act_mask_d,      '0, clk_i, rst_ni);
    `FF(opc_to_eu_operands_addr_q, opc_to_eu_operands_addr_d, '0, clk_i, rst_ni);

    // Request queue
    `FF(req_queue_valid_q, req_queue_valid_d, '0, clk_i, rst_ni);
    `FF(req_queue_q,       req_queue_d,       '0, clk_i, rst_ni);

    // #######################################################################################
    // # Assertions                                                                          #
    // #######################################################################################

    `ifndef SYNTHESIS
        // Check that active mask is never zero
        assert property (@(posedge clk_i) disable iff (!rst_ni)
            opc_to_eu_valid_i |-> opc_to_eu_act_mask_i != '0)
        else $error("Load Store Unit: opc_to_eu_valid_i is high, but opc_to_eu_act_mask_i is zero");

        // Make sure that memory requests ids are unique
        req_id_t requests [$];
        initial begin : check_unique_requests
            while(1) begin
                @(posedge clk_i);
                // Sent request
                if (mem_ready_i && mem_req_valid_o) begin
                    // Check if the request number is unique
                    for(int i = 0; i < requests.size(); i++) begin
                        assert(requests[i] != mem_req_id_o)
                        else $error("Load Store Unit: Duplicate request number %0d", mem_req_id_o);
                    end

                    requests.push_back(mem_req_id_o);
                end
                
                // Response received
                if(mem_rsp_valid_i) begin
                    // Remove the request from the list
                    for(int i = 0; i < requests.size(); i++) begin
                        if (requests[i] == mem_rsp_id_i) begin
                            requests.delete(i);
                            break;
                        end
                    end
                end
            end
        end : check_unique_requests
    `endif

endmodule : load_store_unit
