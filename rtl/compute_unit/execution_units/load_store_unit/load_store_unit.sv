// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "common_cells/registers.svh"

/// Load Store Unit
// Performs load and store operations
// Requests are coalesced into a minimum number of blocks and sent to the memory interface
// in the order that they were received by the Load Store Unit.
// This means that memory ordering has to be checked/enforced by another mechanism.
// Memory responses can be received in any order, but must have atleast one cycle of latency
// Operand 0 is the address for load/store operations
// Operand 1 is the data for store operations
module load_store_unit import bgpu_pkg::*; #(
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
    output block_data_t mem_req_wdata_o,

    /// Memory Response
    input  logic        mem_rsp_valid_i,
    input  req_id_t     mem_rsp_id_i,
    input  block_data_t mem_rsp_data_i,

    /// From Operand Collector
    output logic         eu_to_opc_ready_o,
    input  logic         opc_to_eu_valid_i,
    input  iid_t         opc_to_eu_tag_i,
    input  act_mask_t    opc_to_eu_act_mask_i,
    input  lsu_subtype_e opc_to_eu_inst_sub_i,
    input  reg_idx_t     opc_to_eu_dst_i,
    input  warp_data_t   [OperandsPerInst-1:0] opc_to_eu_operands_i,

    // To Result Collector
    input  logic       rc_to_eu_ready_i,
    output logic       eu_to_rc_valid_o,
    output act_mask_t  eu_to_rc_act_mask_o,
    output iid_t       eu_to_rc_tag_o,
    output reg_idx_t   eu_to_rc_dst_o,
    output warp_data_t eu_to_rc_data_o
);

    // #######################################################################################
    // # Local parameters                                                                    #
    // #######################################################################################

    localparam int unsigned SubReqIdWidth   = WarpWidth > 1 ? $clog2(WarpWidth) : 1;
    localparam int unsigned RegWidthInBytes = RegWidth / 8;
    localparam int unsigned WidthBits       = RegWidthInBytes > 1 ? $clog2(RegWidthInBytes) : 1;
    localparam int unsigned OutstandingReqs = 1 << OutstandingReqIdxWidth;

    // #######################################################################################
    // # Type Definitions                                                                    #
    // #######################################################################################

    typedef logic       [AddressWidth-1:0] addr_t;
    typedef addr_t      [   WarpWidth-1:0] req_addr_t;
    typedef block_idx_t [   WarpWidth-1:0] offsets_t;

    typedef logic [OutstandingReqIdxWidth-1:0] com_req_id_t;
    typedef logic [         SubReqIdWidth-1:0] sub_req_id_t;

    typedef logic [WidthBits-1:0] width_t;
    typedef logic [ RegWidth-1:0] reg_data_t;

    // Data passed from the Coalesce Splitter to the Wdata Assembler
    typedef struct packed {
        com_req_id_t com_id;
        sub_req_id_t sub_id;
        block_addr_t addr;
        logic        is_write;
        warp_data_t  wdata;
        act_mask_t   wdata_valid_mask;
        width_t      write_width;
        block_idx_t [WarpWidth-1:0] offsets;
    } coalesce_splitter_to_wdata_t;

    // Per Thread data
    typedef struct packed {
        sub_req_id_t sub_id;
        block_idx_t  offset;
        reg_data_t   data;
    } thread_data_t;

    // Buffer entry
    typedef struct packed {
        act_mask_t act_mask;
        iid_t      tag;
        reg_idx_t  dst;
        width_t    load_width;
        logic         [WarpWidth-1:0] thread_waiting;
        logic         [WarpWidth-1:0] thread_ready;
        thread_data_t [WarpWidth-1:0] thread_data;
    } buffer_entry_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Do we have space for a new instruction and where in the buffer?
    logic        space_for_new_inst;
    com_req_id_t insert_buff_id;

    // New instruction information
    logic      opc_to_eu_is_write, eu_to_opc_ready;
    req_addr_t opc_to_eu_addr;
    width_t    opc_to_eu_width;

    // Coalesce Splitter to Wdata Assembler
    logic      cs_to_wdata_valid_d, cs_to_wdata_valid_q;
    act_mask_t cs_to_wdata_valid_mask_d;

    logic wdata_to_cs_ready_d, wdata_to_cs_ready_q;
    coalesce_splitter_to_wdata_t cs_to_wdata_d, cs_to_wdata_q;

    // Memory response common and sub ID
    com_req_id_t mem_rsp_com_id;
    sub_req_id_t mem_rsp_sub_id;

    // Request buffer
    logic          [OutstandingReqs-1:0] buffer_valid_q, buffer_valid_d;
    buffer_entry_t [OutstandingReqs-1:0] buffer_q,       buffer_d;

    // Which buffer entries are ready to be sent to the Result Collector
    logic [OutstandingReqs-1:0] buffer_ready_for_rc;
    logic [OutstandingReqs-1:0] buffer_select_for_rc; // Which buffer entries to free
    buffer_entry_t              selected_buffer_entry;

    // #######################################################################################
    // # Combinational logic                                                                 #
    // #######################################################################################

    // Operand 0 is the address for load/store operations
    // Truncate to address width
    for(genvar i = 0; i < WarpWidth; i++) begin : gen_addr
        assign opc_to_eu_addr[i] = opc_to_eu_operands_i[0][i*RegWidth +: AddressWidth];
    end : gen_addr

    // Check if the instruction is a write
    assign opc_to_eu_is_write = opc_to_eu_inst_sub_i inside
        {LSU_STORE_BYTE, LSU_STORE_HALF, LSU_STORE_WORD};

    // Write width
    always_comb begin : operation_width
        opc_to_eu_width = '0; // Default to 1 byte

        case (opc_to_eu_inst_sub_i)
            LSU_STORE_BYTE, LSU_LOAD_BYTE : opc_to_eu_width = 'd0; // 1 byte
            /* verilator lint_off WIDTHTRUNC */
            LSU_STORE_HALF, LSU_LOAD_HALF : begin
                if (RegWidthInBytes >= 2)
                    opc_to_eu_width = 'd1; // 2 bytes
            end
            LSU_STORE_WORD, LSU_LOAD_WORD : begin
                if (RegWidthInBytes >= 4)
                    opc_to_eu_width = 'd2; // 4 bytes
                else if (RegWidthInBytes >= 2)
                    opc_to_eu_width = 'd1; // 2 bytes
            end
            /* verilator lint_on WIDTHTRUNC */
            default : opc_to_eu_width = 'd0; // 1 byte
        endcase
    end : operation_width

    // Check if we have space for a new instruction -> atleast one buffer entry is free
    assign space_for_new_inst = !(&buffer_valid_q);

    // Are only ready if we have space for a new instruction and splitter is ready
    assign eu_to_opc_ready_o = space_for_new_inst && eu_to_opc_ready;

    // Find the first free buffer entry -> Also used as common request ID
    always_comb begin : find_free_buffer_entry
        insert_buff_id = '0; // Default to 0
        for(int unsigned i = 0; i < OutstandingReqs; i++) begin : find_free
            if (!buffer_valid_q[i]) begin
                insert_buff_id = i[OutstandingReqIdxWidth-1:0];
                break; // Found a free entry, stop searching
            end
        end : find_free
    end : find_free_buffer_entry

    // Get common and sub request ID from the memory response
    assign mem_rsp_sub_id = mem_rsp_id_i[SubReqIdWidth-1:0];
    assign mem_rsp_com_id = mem_rsp_id_i[OutstandingReqIdxWidth + SubReqIdWidth-1:SubReqIdWidth];

    // #######################################################################################
    // # Request buffer                                                                      #
    // #######################################################################################

    always_comb begin : request_buffer
        // Default
        buffer_valid_d = buffer_valid_q;
        buffer_d       = buffer_q;

        // If we have a new instruction, set the corresponding buffer entry to valid
        if (opc_to_eu_valid_i && eu_to_opc_ready_o) begin
            buffer_valid_d[insert_buff_id] = 1'b1;

            buffer_d[insert_buff_id].tag        = opc_to_eu_tag_i;
            buffer_d[insert_buff_id].dst        = opc_to_eu_dst_i;
            buffer_d[insert_buff_id].load_width = opc_to_eu_width;
            buffer_d[insert_buff_id].act_mask   = opc_to_eu_act_mask_i;

            // Mark inactive threads as ready
            buffer_d[insert_buff_id].thread_waiting = '0;
            buffer_d[insert_buff_id].thread_ready   = ~opc_to_eu_act_mask_i;
            buffer_d[insert_buff_id].thread_data    = '0; // Clear thread data
        end

        // If we have a request splitted, update the thread data
        if (cs_to_wdata_valid_d && wdata_to_cs_ready_q) begin
            for(int unsigned i = 0; i < WarpWidth; i++) begin : update_thread_data
                if (cs_to_wdata_valid_mask_d[i]) begin
                    // Update the thread data for the corresponding thread
                    buffer_d[cs_to_wdata_d.com_id].thread_data   [i].sub_id = cs_to_wdata_d.sub_id;
                    buffer_d[cs_to_wdata_d.com_id].thread_data   [i].offset
                        = cs_to_wdata_d.offsets[i];
                    buffer_d[cs_to_wdata_d.com_id].thread_waiting[i]        = 1'b1;
                    buffer_d[cs_to_wdata_d.com_id].thread_ready  [i]        = 1'b0;
                end
            end : update_thread_data
        end

        // If we receive a memory response, update the buffer entry
        if (mem_rsp_valid_i) begin
            if (buffer_valid_q[mem_rsp_com_id]) begin
                // If the buffer entry is valid, update the thread data
                for(int unsigned i = 0; i < WarpWidth; i++) begin : update_thread_data_rsp
                    if (!buffer_q[mem_rsp_com_id].thread_ready[i]
                        && buffer_q[mem_rsp_com_id].thread_waiting[i]
                        && buffer_q[mem_rsp_com_id].thread_data[i].sub_id == mem_rsp_sub_id) begin
                        // If the thread is ready and the sub ID matches, update the data
                        // We use the offset to load the correct data
                        // We always load a full register width
                        /* verilator lint_off WIDTHTRUNC */
                        buffer_d[mem_rsp_com_id].thread_data[i].data = mem_rsp_data_i >>
                            (buffer_q[mem_rsp_com_id].thread_data[i].offset * 8);
                        /* verilator lint_on WIDTHTRUNC */

                        buffer_d[mem_rsp_com_id].thread_ready[i] = 1'b1; // Mark thread as ready
                    end
                end : update_thread_data_rsp
            end
        end

        // A buffer entry is selected for the Result Collector
        for(int unsigned i = 0; i < OutstandingReqs; i++) begin : free_buffer
            if (buffer_select_for_rc[i])
                buffer_valid_d[i] = 1'b0; // Free the buffer entry
        end : free_buffer

    end : request_buffer

    // Check if buffer entries are valid and ready to be sent to the Result Collector
    for(genvar i = 0; i < OutstandingReqs; i++) begin : gen_buffer_ready_to_rc
        assign buffer_ready_for_rc[i] = buffer_valid_q[i] && (&buffer_q[i].thread_ready);
    end : gen_buffer_ready_to_rc

    // Arbiter for Result Collector
    rr_arb_tree #(
        .DataType ( buffer_entry_t  ),
        .NumIn    ( OutstandingReqs ),
        .ExtPrio  ( 1'b0 ),
        .AxiVldRdy( 1'b0 ),
        .LockIn   ( 1'b0 ),
        .FairArb  ( 1'b1 )
    ) i_rr_arb (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .req_i ( buffer_ready_for_rc  ),
        .gnt_o ( buffer_select_for_rc ),
        .data_i( buffer_q             ),

        .req_o ( eu_to_rc_valid_o      ),
        .gnt_i ( rc_to_eu_ready_i      ),
        .data_o( selected_buffer_entry ),

        // Unused
        .idx_o  ( /* NOT CONNECTED */ ),
        .flush_i( 1'b0                ),
        .rr_i   ( '0                  )
    );

    // Build output for Result Collector
    assign eu_to_rc_tag_o      = selected_buffer_entry.tag;
    assign eu_to_rc_dst_o      = selected_buffer_entry.dst;
    assign eu_to_rc_act_mask_o = selected_buffer_entry.act_mask;

    always_comb begin : build_warp_data_for_rc
        // Default to zero
        eu_to_rc_data_o = '0;

        // Build the warp data for the Result Collector
        for(int unsigned i = 0; i < WarpWidth; i++) begin : build_warp_data
            /* verilator lint_off WIDTHTRUNC  */
            /* verilator lint_off WIDTHEXPAND */
            if (selected_buffer_entry.load_width == 'd0) begin
                // If the load width is 1 byte, we only take the first byte
                eu_to_rc_data_o[i*RegWidth +: RegWidth] = selected_buffer_entry.thread_data[i].data
                    & 'hff;
            end else if (RegWidthInBytes >= 1 && selected_buffer_entry.load_width == 'd1) begin
                // If the load width is 2 bytes, we take the first two bytes
                eu_to_rc_data_o[i*RegWidth +: RegWidth] = selected_buffer_entry.thread_data[i].data
                    & 'hffff;
            end else if (RegWidthInBytes >= 2 && selected_buffer_entry.load_width == 'd2) begin
                // If the load width is 4 bytes, we take the first four bytes
                eu_to_rc_data_o[i*RegWidth +: RegWidth] = selected_buffer_entry.thread_data[i].data
                    & 'hffffffff;
            end else begin
                `ifndef SYNTHESIS
                    $error("Invalid load width %0d for register width %0d",
                        selected_buffer_entry.load_width, RegWidthInBytes);
                `endif
            end
            /* verilator lint_on WIDTHEXPAND */
            /* verilator lint_on WIDTHTRUNC  */
        end : build_warp_data
    end : build_warp_data_for_rc

    // #######################################################################################
    // # Coalesce Splitter                                                                   #
    // #######################################################################################

    coalesce_splitter #(
        .NumRequests     ( WarpWidth              ),
        .AddressWidth    ( AddressWidth           ),
        .BlockIdxBits    ( BlockIdxBits           ),
        .CommonReqIdWidth( OutstandingReqIdxWidth ),
        .warp_data_t     ( warp_data_t            ),
        .write_width_t   ( width_t                )
    ) i_coalesce_splitter (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .ready_o      ( eu_to_opc_ready                         ),
        .valid_i      ( opc_to_eu_valid_i && space_for_new_inst ),
        .we_i         ( opc_to_eu_is_write                      ),
        .req_id_i     ( insert_buff_id                          ),
        .addr_valid_i ( opc_to_eu_act_mask_i                    ),
        .addr_i       ( opc_to_eu_addr                          ),
        .wdata_i      ( opc_to_eu_operands_i[1]                 ),
        .write_width_i( opc_to_eu_width                         ),

        .req_ready_i      ( wdata_to_cs_ready_q       ),
        .req_valid_o      ( cs_to_wdata_valid_mask_d  ),
        .req_we_o         ( cs_to_wdata_d.is_write    ),
        .req_com_id_o     ( cs_to_wdata_d.com_id      ),
        .req_sub_id_o     ( cs_to_wdata_d.sub_id      ),
        .req_addr_o       ( cs_to_wdata_d.addr        ),
        .req_offsets_o    ( cs_to_wdata_d.offsets     ),
        .req_wdata_o      ( cs_to_wdata_d.wdata       ),
        .req_write_width_o( cs_to_wdata_d.write_width )
    );

    // Valid if atleas one request is valid
    assign cs_to_wdata_valid_d            = |cs_to_wdata_valid_mask_d;
    // Store which threads participate in the write operation
    assign cs_to_wdata_d.wdata_valid_mask = cs_to_wdata_valid_mask_d;

    // #######################################################################################
    // # Register between Coalesce Splitter and Wdata Assembler                              #
    // #######################################################################################

    stream_register #(
        .T( coalesce_splitter_to_wdata_t )
    ) i_cs_to_wdata_reg (
        .clk_i     ( clk_i  ),
        .rst_ni    ( rst_ni ),
        .clr_i     ( 1'b0   ),
        .testmode_i( 1'b0   ),

        .valid_i( cs_to_wdata_valid_d ),
        .ready_o( wdata_to_cs_ready_q ),
        .data_i ( cs_to_wdata_d       ),

        .valid_o( cs_to_wdata_valid_q ),
        .ready_i( wdata_to_cs_ready_d ),
        .data_o ( cs_to_wdata_q       )
    );

    // #######################################################################################
    // # Wdata Assembler                                                                     #
    // #######################################################################################

    wdata_assembler #(
        .RegWidth     ( RegWidth     ),
        .WarpWidth    ( WarpWidth    ),
        .BlockIdxBits ( BlockIdxBits )
    ) i_wdata_assembler (
        .we_mask_i      ( cs_to_wdata_q.is_write ? cs_to_wdata_q.wdata_valid_mask : '0 ),
        .wdata_i        ( cs_to_wdata_q.wdata       ),
        .write_width_i  ( cs_to_wdata_q.write_width ),
        .block_offsets_i( cs_to_wdata_q.offsets     ),

        .mem_we_mask_o( mem_req_we_mask_o ),
        .mem_wdata_o  ( mem_req_wdata_o   )
    );

    // Build the memory request
    assign mem_req_valid_o     = cs_to_wdata_valid_q;
    assign wdata_to_cs_ready_d = mem_ready_i;

    assign mem_req_addr_o = cs_to_wdata_q.addr;
    assign mem_req_id_o   = { cs_to_wdata_q.com_id, cs_to_wdata_q.sub_id };

    // #######################################################################################
    // # Sequential logic                                                                    #
    // #######################################################################################

    // Buffer valid bits
    `FF(buffer_valid_q, buffer_valid_d, '0, clk_i, rst_ni);

    // Buffer entries
    `FF(buffer_q, buffer_d, '0, clk_i, rst_ni);

    // #######################################################################################
    // # Assertions                                                                          #
    // #######################################################################################

    `ifndef SYNTHESIS
        initial assert (RegWidth % 8 == 0)
        else $error("Register width must be a multiple of 8 bits. Current width: %0d", RegWidth);

        initial assert (RegWidth >= AddressWidth)
        else begin
            $display("Register width must be at least as wide as the address width. ");
            $display("Current register width: %0d, address width: %0d", RegWidth, AddressWidth);
            $fatal();
        end

        assert property (@(posedge clk_i) disable iff (!rst_ni)
            opc_to_eu_valid_i && eu_to_opc_ready_o |->
            (opc_to_eu_inst_sub_i inside `INST_STORE)
            || (opc_to_eu_inst_sub_i inside `INST_LOAD)
        ) else $error("Received instruction with invalid type. Tag: %0h, Inst: %0h",
            opc_to_eu_tag_i, opc_to_eu_inst_sub_i);

        assert property (@(posedge clk_i) disable iff (!rst_ni)
            mem_rsp_valid_i |-> buffer_valid_q[mem_rsp_com_id]
        ) else $error("Memory resp received for invalid buffer entry ID %0d", mem_rsp_com_id);

        assert property (@(posedge clk_i) disable iff (!rst_ni)
            mem_rsp_valid_i |-> !(&buffer_q[mem_rsp_com_id].thread_ready)
        ) else $error("Memory resp received for buffer entry ID %0d, but all threads are ready.",
            mem_rsp_com_id);

        assert property (@(posedge clk_i) disable iff (!rst_ni)
            opc_to_eu_valid_i && eu_to_opc_ready_o |-> opc_to_eu_act_mask_i != '0
        ) else $error("Received instruction with no active threads. Tag: %0h, Inst: %0h",
            opc_to_eu_tag_i, opc_to_eu_inst_sub_i);
    `endif

endmodule : load_store_unit
