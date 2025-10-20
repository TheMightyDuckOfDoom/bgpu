// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "common_cells/registers.svh"

/// Wait Buffer
module wait_buffer import bgpu_pkg::*; #(
    /// Number of instructions to fetch for the warp
    parameter int unsigned FetchWidth = 1,
    /// Number of instructions that can write back simultaneously
    parameter int unsigned WritebackWidth = 1,
    /// Number of inflight instructions
    parameter int unsigned NumTags = 8,
    /// Width of the Program Counter
    parameter int unsigned PcWidth = 32,
    /// Number of threads per warp
    parameter int unsigned WarpWidth = 32,
    /// How many instructions that wait on previous results can be buffered per warp
    parameter int unsigned WaitBufferSizePerWarp = 4,
    /// How many registers can each warp access as operand or destination
    parameter int unsigned RegIdxWidth = 6,
    /// How many operands each instruction can have
    parameter int unsigned OperandsPerInst = 2,

    /// Dependent parameter, do **not** overwrite.
    parameter int unsigned TagWidth     = $clog2(NumTags),
    parameter type         tag_t        = logic     [       TagWidth-1:0],
    parameter type         pc_t         = logic     [        PcWidth-1:0],
    parameter type         act_mask_t   = logic     [      WarpWidth-1:0],
    parameter type         reg_idx_t    = logic     [    RegIdxWidth-1:0],
    parameter type         op_mask_t    = logic     [OperandsPerInst-1:0],
    parameter type         op_reg_idx_t = reg_idx_t [OperandsPerInst-1:0],
    parameter type         op_tag_t     = tag_t     [OperandsPerInst-1:0]
) (
    /// Clock and Reset
    input  logic clk_i,
    input  logic rst_ni,

    /// Force instructions to execute in-order
    input  logic inorder_execution_i,

    /// From fetcher |-> which warp gets fetched next
    input  logic fe_handshake_i,

    /// To fetcher |-> space for new instructions?
    output logic [FetchWidth-1:0] ib_space_available_o,

    /// From decoder -> Decoded instruction that does not need a wait buffer entry
    input logic [FetchWidth-1:0] dec_decoded_unused_ibe_i,

    /// From decoder -> new instruction
    output logic        wb_ready_o,
    input  pc_t         dec_pc_i,
    input  act_mask_t   dec_act_mask_i,
    input  logic        [FetchWidth-1:0] dec_valid_i,
    input  tag_t        [FetchWidth-1:0] dec_tag_i,
    input  reg_idx_t    [FetchWidth-1:0] dec_dst_reg_i,
    input  inst_t       [FetchWidth-1:0] dec_inst_i,
    input  op_mask_t    [FetchWidth-1:0] dec_operands_is_reg_i,
    input  op_mask_t    [FetchWidth-1:0] dec_operands_ready_i,
    input  op_tag_t     [FetchWidth-1:0] dec_operand_tags_i,
    input  op_reg_idx_t [FetchWidth-1:0] dec_operands_i,

    /// To Operand Collector
    input  logic        opc_ready_i,
    output logic        disp_valid_o,
    output tag_t        disp_tag_o,
    output pc_t         disp_pc_o,
    output act_mask_t   disp_act_mask_o,
    output inst_t       disp_inst_o,
    output reg_idx_t    disp_dst_o,
    output op_mask_t    disp_operands_is_reg_o,
    output op_reg_idx_t disp_operands_o,

    /// From Operand Collector -> instruction has read its operands
    input logic opc_eu_handshake_i,
    input tag_t opc_eu_tag_i,

    /// From Execution Units
    input logic [WritebackWidth-1:0] eu_valid_i,
    input tag_t [WritebackWidth-1:0] eu_tag_i
);
    // #######################################################################################
    // # Typedefs                                                                            #
    // #######################################################################################

    // Wait Buffer Entry index
    typedef logic [$clog2(WaitBufferSizePerWarp):0] wb_idx_t;

    // Dependency Mask
    typedef logic [WaitBufferSizePerWarp-1:0] entry_mask_t;

    // Entry in the wait buffer per instruction per warp
    typedef struct packed {
        pc_t       pc;
        act_mask_t act_mask;
        tag_t      tag;
        inst_t     inst;
        reg_idx_t  dst_reg;

        // Other instruction that we have to wait for -> allows ordering of instructions
        entry_mask_t dep_mask;

        op_mask_t    operands_is_reg;
        op_mask_t    operands_ready;
        op_tag_t     operand_tags;
        op_reg_idx_t operands;
    } wait_buffer_entry_t;

    typedef struct packed {
        pc_t         pc;
        act_mask_t   act_mask;
        tag_t        tag;
        inst_t       inst;
        reg_idx_t    dst_reg;
        op_mask_t    operands_is_reg;
        op_reg_idx_t operands_reg;
    } disp_data_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Dependecy mask of the new instruction
    entry_mask_t [FetchWidth-1:0] dep_mask;

    // Entry to insert in the wait buffer
    entry_mask_t [FetchWidth-1:0] insert_mask;

    // Which entry gets dispatched in this cycle
    entry_mask_t dispatch_mask;

    // Entry that gets remove in this cycle
    entry_mask_t remove_mask;

    entry_mask_t wait_buffer_valid_q,      wait_buffer_valid_d;
    entry_mask_t wait_buffer_dispatched_q, wait_buffer_dispatched_d;

    wait_buffer_entry_t [WaitBufferSizePerWarp-1:0] wait_buffer_q, wait_buffer_d;

    entry_mask_t rr_inst_ready;
    entry_mask_t arb_gnt;

    disp_data_t [WaitBufferSizePerWarp-1:0] arb_in_data;
    disp_data_t arb_sel_data;

    logic [FetchWidth  :0] give_credit;
    logic [FetchWidth-1:0] take_credit;

    logic    inst_dispatched;
    wb_idx_t credits_left;

    // #######################################################################################
    // # Credit Counter                                                                      #
    // #######################################################################################

    multi_credit_counter #(
        .NumTake        ( FetchWidth            ),
        .NumGive        ( FetchWidth+1          ),
        .NumCredits     ( WaitBufferSizePerWarp ),
        .InitCreditEmpty( 1'b0                  )
    ) i_credit_counter (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .credit_o( credits_left ),

        .credit_take_i( take_credit ),
        .credit_give_i( give_credit ),
        .credit_init_i( 1'b0        ),

        .credit_left_o( /* Unused */ ),
        .credit_crit_o( /* Unused */ ),
        .credit_full_o( /* Unused */ )
    );

    // #######################################################################################
    // # Combinatorial Logic                                                                 #
    // #######################################################################################

    /// Credit counter
    // Decremented when the fetcher sends a request for a new instruction
    // -> Allocate as many as possible up to FetchWidth
    assign inst_dispatched = (|arb_gnt) && disp_valid_o && opc_ready_i;
    
    // Incremented when the instruction get dispatched to the operand collector
    // or the decoder indicates that no buffer space for the instruction was needed
    // (control or was unable to fetch from cache)
    assign give_credit           [0] = inst_dispatched;
    assign give_credit[FetchWidth:1] = dec_decoded_unused_ibe_i;

    // Take credits when a fetcher handshake happens
    assign take_credit = fe_handshake_i ? ib_space_available_o : '0;

    // How many instructions can be inserted into the wait buffer?
    // Ones are continous from LSB side
    always_comb begin : space_available_logic
        ib_space_available_o = '0;
        for (int fidx = 0; fidx < FetchWidth; fidx++) begin : loop_fetch_width
            if (credits_left > wb_idx_t'(fidx))
                ib_space_available_o[fidx] = 1'b1;
        end : loop_fetch_width
    end : space_available_logic

    // Wait buffer is ready if there is space available
    assign wb_ready_o = !(&wait_buffer_valid_q);

    // Determine which entry to insert
    always_comb begin : build_insert_mask
        insert_mask = '0;
        for (int fidx = 0; fidx < FetchWidth; fidx++) begin : gen_insert_mask_per_fetch
            for (int i = 0; i < WaitBufferSizePerWarp; i++) begin : loop_entries
                if (!wait_buffer_valid_q[i]) begin
                    insert_mask[fidx][i] = 1'b1;
                    break;
                end
            end : loop_entries
        end : gen_insert_mask_per_fetch
    end : build_insert_mask

    // Which entry to dispatch in this cycle
    assign dispatch_mask = arb_gnt & rr_inst_ready;

    // Build dependency mask
    always_comb begin : build_dep_mask
        dep_mask = '0;

        // Inorder execution, all instructions are dependent on the previous ones
        if (inorder_execution_i) begin : inorder_execution
            for (int fidx = 0; fidx < FetchWidth; fidx++) begin : gen_inorder_dep
                if (fidx == 0) begin
                    // First instruction depends on all instructions in the wait buffer
                    dep_mask[fidx] = wait_buffer_valid_q;
                end else begin
                    // Subsequent instructions depend on all previous instructions in this fetch
                    dep_mask[fidx] = dep_mask[fidx-1] | insert_mask[fidx-1];
                end
            end : gen_inorder_dep
        end : inorder_execution

        // Out of order execution
        // Need to guard agains WAR and WAW hazards
        // Write to a register before it has been read
        else begin : out_of_order_execution
            // TODO: For now we only support FetchWidth == 1
            assert(FetchWidth == 1) else $error("Out of order execution with FetchWidth > 1 is not supported yet");

            // If the destination of the new instruction is used as operand in the wait buffer,
            // then we have to wait for it to be executed to avoid WAR hazards

            // If the desitination of the new instructions is the same as a previous instruction,
            // then we have to wait for it to be executed to avoid WAW hazards
            for (int i = 0; i < WaitBufferSizePerWarp; i++) begin : gen_dep_mask
                if (wait_buffer_valid_q[i]) begin : check_entry
                    // Check if the destination register is used as operand in the wait buffer
                    for (int operand = 0; operand < OperandsPerInst; operand++) begin : gen_operand_check
                        if (wait_buffer_q[i].operands_is_reg[operand]
                        && wait_buffer_q[i].operands[operand] == dec_dst_reg_i) begin
                            dep_mask[0][i] = 1'b1;
                        end
                    end : gen_operand_check

                    // Check if the destination register is the same as the new instruction
                    if (wait_buffer_q[i].dst_reg == dec_dst_reg_i) begin
                        dep_mask[i] = 1'b1;
                    end
                end : check_entry
            end : gen_dep_mask
        end : out_of_order_execution
    end : build_dep_mask

    // Build the remove mask
    always_comb begin : build_remove_mask
        remove_mask = '0;

        if (opc_eu_handshake_i) begin
            for (int i = 0; i < WaitBufferSizePerWarp; i++) begin : gen_remove_mask
                if (wait_buffer_valid_q[i]
                  && wait_buffer_dispatched_q[i]
                  && wait_buffer_q[i].tag == opc_eu_tag_i) begin
                    remove_mask[i] = 1'b1;
                end
            end : gen_remove_mask
        end
    end : build_remove_mask

    // Wait Buffer Entry Logic
    for (genvar entry = 0; entry < WaitBufferSizePerWarp; entry++) begin : gen_insert_logic
        always_comb begin
            // Default
            wait_buffer_d           [entry] = wait_buffer_q           [entry];
            wait_buffer_valid_d     [entry] = wait_buffer_valid_q     [entry];
            wait_buffer_dispatched_d[entry] = wait_buffer_dispatched_q[entry];

            // Dispatch: Mark the instruction as dispatched
            if (dispatch_mask[entry]) begin : mark_dispatched
                wait_buffer_dispatched_d[entry] = 1'b1;
            end : mark_dispatched

            // Remove the instruction from the wait buffer
            if (remove_mask[entry]) begin : remove_entry
                wait_buffer_valid_d[entry] = 1'b0;
            end : remove_entry

            // Clear dependency bit
            if (remove_mask != '0) begin : clear_dep_mask
                wait_buffer_d[entry].dep_mask = wait_buffer_q[entry].dep_mask & (~remove_mask);
            end : clear_dep_mask

            // From Execution Units
            for (int wb = 0; wb < WritebackWidth; wb++) begin : check_wb_operands
                if (eu_valid_i[wb]) begin : check_operands
                    if (wait_buffer_valid_q[entry]) begin
                        // Check if the instruction produced an operand
                        for (int operand = 0; operand < OperandsPerInst; operand++) begin
                            if (!wait_buffer_q[entry].operands_ready[operand]
                            && wait_buffer_q[entry].operand_tags[operand] == eu_tag_i[wb]) begin
                                wait_buffer_d[entry].operands_ready[operand] = 1'b1;
                            end
                        end
                    end
                end : check_operands
            end : check_wb_operands

            // Insert instruction into buffer
            for (int fidx = 0; fidx < FetchWidth; fidx++) begin : insert_entry_per_fetch
                if (dec_valid_i && wb_ready_o && insert_mask[fidx][entry]) begin : insert_entry
                    wait_buffer_valid_d     [entry] = 1'b1;
                    wait_buffer_dispatched_d[entry] = 1'b0;

                    wait_buffer_d[entry].pc       = dec_pc_i + fidx[PcWidth-1:0]; // Adjust PC for fetch index
                    wait_buffer_d[entry].act_mask = dec_act_mask_i;
                    wait_buffer_d[entry].inst     = dec_inst_i   [fidx];
                    wait_buffer_d[entry].dst_reg  = dec_dst_reg_i[fidx];
                    wait_buffer_d[entry].tag      = dec_tag_i    [fidx];

                    wait_buffer_d[entry].dep_mask = dep_mask[fidx] & (~remove_mask);

                    wait_buffer_d[entry].operands_is_reg = dec_operands_is_reg_i[fidx];
                    wait_buffer_d[entry].operands_ready  = dec_operands_ready_i[fidx]
                                                        | (~dec_operands_is_reg_i[fidx]);

                    wait_buffer_d[entry].operands     = dec_operands_i    [fidx];
                    wait_buffer_d[entry].operand_tags = dec_operand_tags_i[fidx];
                end : insert_entry
            end : insert_entry_per_fetch
        end
    end : gen_insert_logic

    // Which instruction is ready to be dispatched?
    for (genvar entry = 0; entry < WaitBufferSizePerWarp; entry++) begin : gen_rr_inst_ready
        assign rr_inst_ready[entry]            = wait_buffer_valid_q[entry]
                                                    && &wait_buffer_q[entry].operands_ready
                                                    && !wait_buffer_dispatched_q[entry]
                                                    && (wait_buffer_q[entry].dep_mask == '0);
        assign arb_in_data[entry].pc              = wait_buffer_q[entry].pc;
        assign arb_in_data[entry].act_mask        = wait_buffer_q[entry].act_mask;
        assign arb_in_data[entry].tag             = wait_buffer_q[entry].tag;
        assign arb_in_data[entry].inst            = wait_buffer_q[entry].inst;
        assign arb_in_data[entry].dst_reg         = wait_buffer_q[entry].dst_reg;
        assign arb_in_data[entry].operands_is_reg = wait_buffer_q[entry].operands_is_reg;
        assign arb_in_data[entry].operands_reg    = wait_buffer_q[entry].operands;
    end : gen_rr_inst_ready

    // Round robin arbiter
    rr_arb_tree #(
        .DataType ( disp_data_t ),
        .NumIn    ( WaitBufferSizePerWarp ),
        .ExtPrio  ( 1'b0 ),
        .AxiVldRdy( 1'b0 ),
        .LockIn   ( 1'b0 ),
        .FairArb  ( 1'b1 )
    ) i_rr_arb (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .req_i  ( rr_inst_ready ),
        .gnt_o  ( arb_gnt       ),
        .data_i ( arb_in_data   ),

        // Directly to Operand Collector
        .req_o ( disp_valid_o ),
        .gnt_i ( opc_ready_i  ),
        .data_o( arb_sel_data ),

        // Unused
        .idx_o  (      ),
        .flush_i( 1'b0 ),
        .rr_i   ( '0   )
    );

    assign disp_pc_o              = arb_sel_data.pc;
    assign disp_act_mask_o        = arb_sel_data.act_mask;
    assign disp_tag_o             = arb_sel_data.tag;
    assign disp_inst_o            = arb_sel_data.inst;
    assign disp_dst_o             = arb_sel_data.dst_reg;
    assign disp_operands_is_reg_o = arb_sel_data.operands_is_reg;
    assign disp_operands_o        = arb_sel_data.operands_reg;

    // #######################################################################################
    // # Sequential Logic                                                                    #
    // #######################################################################################

    `FF(wait_buffer_valid_q,      wait_buffer_valid_d,      '0, clk_i, rst_ni)
    `FF(wait_buffer_dispatched_q, wait_buffer_dispatched_d, '0, clk_i, rst_ni)
    `FF(wait_buffer_q,            wait_buffer_d,            '0, clk_i, rst_ni)

    // #######################################################################################
    // # Assertions                                                                         #
    // #######################################################################################

    `ifndef SYNTHESIS
        // Check if the instruction buffer is ready to accept new instructions
        // It should always be ready, as otherwise the fetcher would not be informed that there is
        // space available
        assert property (@(posedge clk_i) disable iff(!rst_ni) dec_valid_i |-> wb_ready_o)
        else $error("Instruction buffer is not ready");

        // If we have a output handshake, then one instruction has to be selected for dispatch
        assert property (@(posedge clk_i) disable iff(!rst_ni) disp_valid_o && opc_ready_i
            |-> |arb_gnt)
        else $error("No instruction selected for dispatch");

        // Remove mask can only have one or no bits set
        assert property (@(posedge clk_i) disable iff(!rst_ni)
            (remove_mask == '0 || $onehot(remove_mask)))
        else $error("Remove mask has more than one bit set");

        // Dispatch mask can only have one or no bits set
        assert property (@(posedge clk_i) disable iff(!rst_ni)
            (dispatch_mask == '0 || $onehot(dispatch_mask)))
        else $error("Dispatch mask has more than one bit set");

        // Insert mask can only have one or no bits set
        for (genvar fidx = 0; fidx < FetchWidth; fidx++) begin : gen_assert_insert_mask_per_fetch
            assert property (@(posedge clk_i) disable iff(!rst_ni)
                (insert_mask[fidx] == '0 || $onehot(insert_mask[fidx])))
            else $error("Insert mask %0d has more than one bit set", fidx);
        end : gen_assert_insert_mask_per_fetch

        // Generate assertions for each wait buffer entry
        for (genvar i = 0; i < WaitBufferSizePerWarp; i++) begin : gen_asserts
            // Assert that the arbiter only grants valid instructions
            assert property (@(posedge clk_i) disable iff(!rst_ni)
                arb_gnt[i] && rr_inst_ready[i] |-> wait_buffer_valid_q[i])
            else $error("Arbiter granted an instruction that is not valid in the wait buffer");

            // Operands have to be ready when the arbiter grants the instruction
            assert property (@(posedge clk_i) disable iff(!rst_ni)
                arb_gnt[i] && rr_inst_ready[i] |-> &wait_buffer_q[i].operands_ready)
            else $error("Arbiter granted an instruction that is not ready in the wait buffer");

            // Assert that the wait buffer at the index is empty when the fetcher tries to insert an instruction
            for (genvar fidx = 0; fidx < FetchWidth; fidx++) begin : gen_insert_asserts_per_fetch
                assert property (@(posedge clk_i) disable iff(!rst_ni)
                    dec_valid_i && wb_ready_o && insert_mask[fidx][i] |-> !wait_buffer_valid_q[i])
                else $error("Insert index %0d for insert %0d is already valid in the wait buffer", i, fidx);
            end : gen_insert_asserts_per_fetch

            for (genvar j = 0; j < WaitBufferSizePerWarp; j++) begin : gen_cross_entry_asserts
                // Assert that the dependency mask is only set for valid instructions
                assert property (@(posedge clk_i) disable iff(!rst_ni)
                    wait_buffer_valid_q[i] && wait_buffer_q[i].dep_mask[j]
                    |-> wait_buffer_valid_q[j])
                else $error("Dependency mask is set for an invalid instruction in the wait buffer");

                // Assert that there are no two entries with the same tag
                assert property (@(posedge clk_i) disable iff(!rst_ni)
                    wait_buffer_valid_q[i] && wait_buffer_q[i].tag == wait_buffer_q[j].tag
                    && i != j |-> !wait_buffer_valid_q[j])
                else $error("Two entries in the wait buffer have the same tag %0d, entries %d %d",
                    wait_buffer_q[i].tag, i, j);
            end : gen_cross_entry_asserts
        end : gen_asserts
    `endif

endmodule : wait_buffer
