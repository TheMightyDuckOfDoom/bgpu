// Copyright March 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Wait Buffer
module wait_buffer #(
    parameter int NumTags = 8,
    /// Width of the Program Counter
    parameter int PcWidth = 32,
    /// Number of threads per warp
    parameter int WarpWidth = 32,
    /// How many instructions that wait on previous results can be buffered per warp
    parameter int WaitBufferSizePerWarp = 4,
    /// How many registers can each warp access as operand or destination
    parameter int RegIdxWidth = 6,
    /// How many operands each instruction can have
    parameter int OperandsPerInst = 2,

    /// Dependent parameter, do **not** overwrite.
    parameter int  TagWidth   = $clog2(NumTags),
    parameter type tag_t      = logic [   TagWidth-1:0],  
    parameter type pc_t       = logic [    PcWidth-1:0],
    parameter type act_mask_t = logic [  WarpWidth-1:0],
    parameter type reg_idx_t  = logic [RegIdxWidth-1:0]
) (
    /// Clock and Reset
    input  logic clk_i,
    input  logic rst_ni,

    /// From fetcher -> which warp gets fetched next
    input  logic fe_handshake_i,

    /// From decoder
    output logic      wb_ready_o,
    input  logic      dec_valid_i,
    input  pc_t       dec_pc_i,
    input  act_mask_t dec_act_mask_i,
    input  tag_t      dec_tag_i,
    input  reg_idx_t  dec_dst_reg_i,
    input  logic    [OperandsPerInst-1:0] dec_operands_ready_i,
    input  tag_t    [OperandsPerInst-1:0] dec_operand_tags_i,
    input  reg_idx_t[OperandsPerInst-1:0] dec_operands_i,

    /// To fetcher -> space for a new instruction?
    output logic ib_space_available_o
);
    // #######################################################################################
    // # Typedefs                                                                            #
    // #######################################################################################

    // Entry in the wait buffer per instruction per warp
    typedef struct packed {
        pc_t pc;
        act_mask_t act_mask;

        tag_t tag;
        reg_idx_t dst_reg;

        logic     [OperandsPerInst-1:0] operands_ready;
        tag_t     [OperandsPerInst-1:0] operand_tags;
        reg_idx_t [OperandsPerInst-1:0] operands;
    } wait_buffer_entry_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    logic [WaitBufferSizePerWarp-1:0] wait_buffer_valid_q, wait_buffer_valid_d;
    wait_buffer_entry_t [WaitBufferSizePerWarp-1:0] wait_buffer_q, wait_buffer_d;

    // #######################################################################################
    // # Combinatorial Logic                                                                 #
    // #######################################################################################

    // Credit counter
    // Decremented when an instruction is fetched for the warp
    // Incremented when the instruction get dispatched to the operand collector
    credit_counter #(
        .NumCredits     ( WaitBufferSizePerWarp ),
        .InitCreditEmpty( 1'b0                  )
    ) cc (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .credit_take_i( fe_handshake_i ),
        .credit_give_i( 1'b0 ),
        .credit_init_i( 1'b0 ),

        .credit_left_o( ib_space_available_o ),
        // Not used
        .credit_o     (),
        .credit_crit_o(),
        .credit_full_o()
    );

    // Wait buffer is ready if there is space available
    assign wb_ready_o = !(&wait_buffer_valid_q);

    // Buffer logic
    always_comb begin : wait_buffer_logic
        // Default
        wait_buffer_valid_d = wait_buffer_valid_q;
        wait_buffer_d       = wait_buffer_q;

        // Insert instruction into buffer
        if(dec_valid_i && wb_ready_o) begin : insert_instruction
            // Find first free entry
            for(integer entry = 0; entry < WaitBufferSizePerWarp; entry++) begin
                if(!wait_buffer_valid_q[entry]) begin
                    wait_buffer_valid_d[entry]          = 1'b1;
                    wait_buffer_d[entry].pc             = dec_pc_i;
                    wait_buffer_d[entry].act_mask       = dec_act_mask_i;
                    wait_buffer_d[entry].operands_ready = dec_operands_ready_i;
                    wait_buffer_d[entry].operands       = dec_operands_i;
                    wait_buffer_d[entry].operand_tags   = dec_operand_tags_i;
                    wait_buffer_d[entry].dst_reg        = dec_dst_reg_i;
                    wait_buffer_d[entry].tag            = dec_tag_i;
                    break;
                end
            end
        end : insert_instruction
    end : wait_buffer_logic

    // #######################################################################################
    // # Sequential Logic                                                                    #
    // #######################################################################################

    for(genvar i = 0; i < WaitBufferSizePerWarp; i++) begin : gen_buffer_ff
        `FF(wait_buffer_valid_q[i], wait_buffer_valid_d[i], '0, clk_i, rst_ni);
        `FF(wait_buffer_q[i], wait_buffer_d[i], '0, clk_i, rst_ni);
    end : gen_buffer_ff

    // #######################################################################################
    // # Assertions                                                                         #
    // #######################################################################################

    // Check if the instruction buffer is ready to accept new instructions
    // It should always be ready, as otherwise the fetcher would not be informed that there is
    // space available
    assert property (@(posedge clk_i) disable iff(!rst_ni) dec_valid_i |-> wb_ready_o)
    else $fatal("Instruction buffer is not ready");

endmodule : wait_buffer
