// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "bgpu/instructions.svh"
`include "common_cells/registers.svh"

/// Wait Buffer
module wait_buffer #(
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
    parameter int unsigned TagWidth   = $clog2(NumTags),
    parameter type         tag_t      = logic [   TagWidth-1:0],
    parameter type         pc_t       = logic [    PcWidth-1:0],
    parameter type         act_mask_t = logic [  WarpWidth-1:0],
    parameter type         reg_idx_t  = logic [RegIdxWidth-1:0]
) (
    /// Clock and Reset
    input  logic clk_i,
    input  logic rst_ni,

    /// From fetcher |-> which warp gets fetched next
    input  logic fe_handshake_i,

    /// To fetcher |-> space for a new instruction?
    output logic ib_space_available_o,

    /// From decoder
    output logic       wb_ready_o,
    input  logic       dec_valid_i,
    input  pc_t        dec_pc_i,
    input  act_mask_t  dec_act_mask_i,
    input  tag_t       dec_tag_i,
    input  reg_idx_t   dec_dst_reg_i,
    input  bgpu_inst_t dec_inst_i,
    input  logic       [OperandsPerInst-1:0] dec_operands_ready_i,
    input  tag_t       [OperandsPerInst-1:0] dec_operand_tags_i,
    input  reg_idx_t   [OperandsPerInst-1:0] dec_operands_i,

    /// To Operand Collector
    input  logic       opc_ready_i,
    output logic       disp_valid_o,
    output tag_t       disp_tag_o,
    output pc_t        disp_pc_o,
    output act_mask_t  disp_act_mask_o,
    output bgpu_inst_t disp_inst_o,
    output reg_idx_t   disp_dst_o,
    output reg_idx_t   [OperandsPerInst-1:0] disp_operands_o,

    /// From Execution Units
    input  logic eu_valid_i,
    input  tag_t eu_tag_i
);
    localparam int WaitBufferIndexWidth
        = WaitBufferSizePerWarp > 1 ? $clog2(WaitBufferSizePerWarp) : 1;

    // #######################################################################################
    // # Typedefs                                                                            #
    // #######################################################################################

    // Entry in the wait buffer per instruction per warp
    typedef struct packed {
        pc_t        pc;
        act_mask_t  act_mask;
        tag_t       tag;
        bgpu_inst_t inst;
        reg_idx_t   dst_reg;

        logic     [OperandsPerInst-1:0] operands_ready;
        tag_t     [OperandsPerInst-1:0] operand_tags;
        reg_idx_t [OperandsPerInst-1:0] operands;
    } wait_buffer_entry_t;

    typedef struct packed {
        pc_t        pc;
        act_mask_t  act_mask;
        tag_t       tag;
        bgpu_inst_t inst;
        reg_idx_t   dst_reg;
        reg_idx_t   [OperandsPerInst-1:0] operands_reg;
    } disp_data_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    logic               [WaitBufferSizePerWarp-1:0] wait_buffer_valid_q, wait_buffer_valid_d;
    wait_buffer_entry_t [WaitBufferSizePerWarp-1:0] wait_buffer_q,       wait_buffer_d;

    logic       [WaitBufferSizePerWarp-1:0] rr_inst_ready;
    logic       [WaitBufferSizePerWarp-1:0] arb_gnt;
    disp_data_t [WaitBufferSizePerWarp-1:0] arb_in_data;
    disp_data_t arb_sel_data;

    // #######################################################################################
    // # Combinatorial Logic                                                                 #
    // #######################################################################################

    // Credit counter
    // Decremented when an instruction is fetched for the warp
    // Incremented when the instruction get dispatched to the operand collector
    credit_counter #(
        .NumCredits     ( WaitBufferSizePerWarp ),
        .InitCreditEmpty( 1'b0                  )
    ) i_credit_counter (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .credit_take_i( fe_handshake_i ),
        .credit_give_i( |arb_gnt && disp_valid_o && opc_ready_i ),
        .credit_init_i( 1'b0 ),

        .credit_left_o( ib_space_available_o ),
        // Not used
        .credit_o     ( /* NOT CONNECTED */ ),
        .credit_crit_o( /* NOT CONNECTED */ ),
        .credit_full_o( /* NOT CONNECTED */ )
    );

    // Wait buffer is ready if there is space available
    assign wb_ready_o = !(&wait_buffer_valid_q);

    logic [WaitBufferIndexWidth-1:0] insert_idx;
    always_comb begin
        insert_idx = '0;
        for(int i = 0; i < WaitBufferSizePerWarp; i++) begin
            if(!wait_buffer_valid_q[i]) begin
                insert_idx = i[WaitBufferIndexWidth-1:0];
                break;
            end
        end
    end

    for(genvar entry = 0; entry < WaitBufferSizePerWarp; entry++) begin : gen_insert_logic
        always_comb begin
            // Default
            wait_buffer_d      [entry] = wait_buffer_q[entry];
            wait_buffer_valid_d[entry] = wait_buffer_valid_q[entry];

            // Dispatch: Remove instruction from buffer
            if(arb_gnt[entry] && rr_inst_ready[entry]) begin
                wait_buffer_valid_d[entry] = 1'b0;
            end
            // From Execution Units
            if(eu_valid_i) begin : check_ready
                if(wait_buffer_valid_q[entry]) begin
                    for(int operand = 0; operand < OperandsPerInst; operand++) begin
                        if(!wait_buffer_q[entry].operands_ready[operand]
                          && wait_buffer_q[entry].operand_tags[operand] == eu_tag_i) begin
                            wait_buffer_d[entry].operands_ready[operand] = 1'b1;
                        end
                    end
                end
            end : check_ready

            // Insert instruction into buffer
            if(dec_valid_i && wb_ready_o && insert_idx == entry) begin
                wait_buffer_valid_d[entry]          = 1'b1;
                wait_buffer_d[entry].pc             = dec_pc_i;
                wait_buffer_d[entry].act_mask       = dec_act_mask_i;
                wait_buffer_d[entry].operands_ready = dec_operands_ready_i;
                wait_buffer_d[entry].operands       = dec_operands_i;
                wait_buffer_d[entry].operand_tags   = dec_operand_tags_i;
                wait_buffer_d[entry].inst           = dec_inst_i;
                wait_buffer_d[entry].dst_reg        = dec_dst_reg_i;
                wait_buffer_d[entry].tag            = dec_tag_i;
            end
        end
    end : gen_insert_logic

    // Which instruction is ready to be dispatched?
    for(genvar entry = 0; entry < WaitBufferSizePerWarp; entry++) begin : gen_rr_inst_ready
        assign rr_inst_ready[entry]            = wait_buffer_valid_q[entry]
                                                    && &wait_buffer_q[entry].operands_ready;
        assign arb_in_data[entry].pc           = wait_buffer_q[entry].pc;
        assign arb_in_data[entry].act_mask     = wait_buffer_q[entry].act_mask;
        assign arb_in_data[entry].tag          = wait_buffer_q[entry].tag;
        assign arb_in_data[entry].inst         = wait_buffer_q[entry].inst;
        assign arb_in_data[entry].dst_reg      = wait_buffer_q[entry].dst_reg;
        assign arb_in_data[entry].operands_reg = wait_buffer_q[entry].operands;
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

    assign disp_pc_o       = arb_sel_data.pc;
    assign disp_act_mask_o = arb_sel_data.act_mask;
    assign disp_tag_o      = arb_sel_data.tag;
    assign disp_inst_o     = arb_sel_data.inst;
    assign disp_dst_o      = arb_sel_data.dst_reg;
    assign disp_operands_o = arb_sel_data.operands_reg;

    // #######################################################################################
    // # Sequential Logic                                                                    #
    // #######################################################################################

    `FF(wait_buffer_valid_q, wait_buffer_valid_d, '0, clk_i, rst_ni);
    for(genvar i = 0; i < WaitBufferSizePerWarp; i++) begin : gen_buffer_ff
        `FF(wait_buffer_q[i], wait_buffer_d[i], '0, clk_i, rst_ni);
    end : gen_buffer_ff

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
            assert property (@(posedge clk_i) disable iff(!rst_ni)
                dec_valid_i && wb_ready_o |-> !wait_buffer_valid_q[insert_idx])
            else $error("Insert index is already valid in the wait buffer");
        end : gen_asserts
    `endif

endmodule : wait_buffer
