// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Multi Warp Dispatcher
/// Contains a dispatcher per warp
module multi_warp_dispatcher import bgpu_pkg::*; #(
    /// Number of instructions to fetch for the warp
    parameter int unsigned FetchWidth = 1,
    /// Number of instructions to dispatch simultaneously
    // Each warp dispatches atmost one instruction per cycle -> saves complexity in dispatcher
    // but multiple warps can dispatch simultaneously
    parameter int unsigned DispatchWidth = 1,
    /// Number of instructions that can write back simultaneously
    parameter int unsigned WritebackWidth = 1,
    /// Number of inflight instructions per warp
    parameter int unsigned NumTags = 8,
    /// Width of the Program Counter
    parameter int unsigned PcWidth = 32,
    /// Number of warps per compute unit
    parameter int unsigned NumWarps = 8,
    /// Number of threads per warp
    parameter int unsigned WarpWidth = 32,
    /// How many registers can each warp access as operand or destination
    parameter int unsigned RegIdxWidth = 6,
    /// How many operands each instruction can have
    parameter int unsigned OperandsPerInst = 2,

    /// Dependent parameter, do **not** overwrite.
    parameter int unsigned TagWidth       = $clog2(NumTags),
    parameter int unsigned WidWidth       =  NumWarps > 1 ? $clog2(NumWarps)  : 1,
    parameter int unsigned SubwarpIdWidth = WarpWidth > 1 ? $clog2(WarpWidth) : 1,
    parameter type         wid_t          = logic     [         WidWidth-1:0],
    parameter type         reg_idx_t      = logic     [      RegIdxWidth-1:0],
    parameter type         pc_t           = logic     [          PcWidth-1:0],
    parameter type         act_mask_t     = logic     [        WarpWidth-1:0],
    parameter type         tag_t          = logic     [         TagWidth-1:0],
    parameter type         iid_t          = logic     [TagWidth+WidWidth-1:0],
    parameter type         subwarp_id_t   = logic     [   SubwarpIdWidth-1:0],
    parameter type         fetch_mask_t   = logic     [       FetchWidth-1:0],
    parameter type         op_is_reg_t    = logic     [  OperandsPerInst-1:0],
    parameter type         op_reg_idx_t   = reg_idx_t [  OperandsPerInst-1:0]
) (
    /// Clock and Reset
    input  logic clk_i,
    input  logic rst_ni,

    /// Force instructions to execute in-order
    input  logic inorder_execution_i,

    /// From fetcher |-> which warp gets fetched next
    input  logic fe_handshake_i,
    input  wid_t fe_warp_id_i,

    /// To fetcher
    // |-> which warps have space for a new instruction?
    output fetch_mask_t [NumWarps-1:0] ib_space_available_o,
    // Are there any instructions in flight?
    output logic [NumWarps-1:0] ib_all_instr_finished_o,

    /// From decoder -> Decoded instruction that does not need a wait buffer entry
    input  logic        dec_decoded_i,
    input  fetch_mask_t dec_decoded_unused_ibe_i,
    input  wid_t        dec_decoded_warp_id_i,

    /// From decoder -> new instruction
    output logic                         ib_ready_o,
    input  logic                         dec_valid_i,
    input  pc_t                          dec_pc_i,
    input  act_mask_t                    dec_act_mask_i,
    input  wid_t                         dec_warp_id_i,
    input  subwarp_id_t                  dec_subwarp_id_i,
    input  logic        [FetchWidth-1:0] dec_valid_insts_i,
    input  inst_t       [FetchWidth-1:0] dec_inst_i,
    input  reg_idx_t    [FetchWidth-1:0] dec_dst_i,
    input  op_is_reg_t  [FetchWidth-1:0] dec_operands_is_reg_i,
    input  op_reg_idx_t [FetchWidth-1:0] dec_operands_i,

    /// To Operand Collector
    input  logic        [DispatchWidth-1:0] opc_ready_i,
    output logic        [DispatchWidth-1:0] disp_valid_o,
    output iid_t        [DispatchWidth-1:0] disp_tag_o,
    output pc_t         [DispatchWidth-1:0] disp_pc_o,
    output act_mask_t   [DispatchWidth-1:0] disp_act_mask_o,
    output inst_t       [DispatchWidth-1:0] disp_inst_o,
    output reg_idx_t    [DispatchWidth-1:0] disp_dst_o,
    output op_is_reg_t  [DispatchWidth-1:0] disp_operands_is_reg_o,
    output op_reg_idx_t [DispatchWidth-1:0] disp_operands_o,

    /// From Operand Collector -> instruction has read its operands
    input logic [DispatchWidth-1:0] opc_eu_handshake_i,
    input iid_t [DispatchWidth-1:0] opc_eu_tag_i,

    /// From Execution Units
    input  logic [WritebackWidth-1:0] eu_valid_i,
    input  iid_t [WritebackWidth-1:0] eu_tag_i
);
    // #######################################################################################
    // # Typedefs                                                                            #
    // #######################################################################################

    typedef logic [NumWarps-1:0] warp_mask_t;

    typedef struct packed {
        tag_t      tag;
        pc_t       pc;
        act_mask_t act_mask;
        inst_t     inst;
        reg_idx_t  dst_reg;
        logic      [OperandsPerInst-1:0] operands_is_reg;
        reg_idx_t  [OperandsPerInst-1:0] operands;
    } disp_data_t;

    typedef logic [WritebackWidth-1:0] eu_valid_vec_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Dispatcher per warp
    warp_mask_t dec_valid_warp, ib_ready_warp, fe_handshake_warp;

    eu_valid_vec_t [NumWarps-1:0] eu_valid;
    tag_t [WritebackWidth-1:0] eu_tag;

    // Round Robin Arbiter
    warp_mask_t arb_gnts;
    warp_mask_t [DispatchWidth-1:0] arb_gnt;
    warp_mask_t [DispatchWidth-1:0] rr_inst_ready;

    wid_t       [DispatchWidth-1:0] arb_sel_wid;
    disp_data_t [DispatchWidth-1:0] arb_sel_data;
    disp_data_t [NumWarps-1:0] arb_in_data;

    // Decoded Demultiplexer
    fetch_mask_t [NumWarps-1:0] dec_decoded_unused_ibe;

    // OPC EU Handshake Demultiplexer
    warp_mask_t opc_eu_handshake_warp;
    tag_t [NumWarps-1:0] opc_eu_tag;

    // #######################################################################################
    // # Dispatcher per warp                                                                 #
    // #######################################################################################

    // Decoder Valid Demultiplexer
    always_comb begin
        dec_valid_warp = '0;
        dec_valid_warp[dec_warp_id_i] = dec_valid_i;
    end

    // Instruction Buffer Ready Multiplexer
    always_comb begin
        ib_ready_o  = '0;
        ib_ready_o = ib_ready_warp[dec_warp_id_i];
    end

    // Fetcher Handshake Demultiplexer
    always_comb begin
        fe_handshake_warp = '0;
        fe_handshake_warp[fe_warp_id_i] = fe_handshake_i;
    end

    // Execution Unit Valid Demultiplexer
    always_comb begin
        eu_valid = '0;
        for (int warp = 0; warp < NumWarps; warp++) begin : loop_warps
            for (int wb = 0; wb < WritebackWidth; wb++)
                eu_valid[warp][wb] = eu_valid_i[wb]
                                     && (eu_tag_i[wb][WidWidth-1:0] == warp[WidWidth-1:0]);
        end : loop_warps
    end

    // Decoder Decoded Demultiplexer
    always_comb begin
        dec_decoded_unused_ibe = '0;
        if (dec_decoded_i)
            dec_decoded_unused_ibe[dec_decoded_warp_id_i] = dec_decoded_unused_ibe_i;
    end

    // OPC EU Handshake Demultiplexer
    always_comb begin
        opc_eu_handshake_warp = '0;
        opc_eu_tag = '0;
        for (int didx = 0; didx < DispatchWidth; didx++) begin
            if (opc_eu_handshake_i[didx]) begin
                opc_eu_handshake_warp[opc_eu_tag_i[didx][WidWidth-1:0]] = 1'b1;
                opc_eu_tag[opc_eu_tag_i[didx][WidWidth-1:0]] = opc_eu_tag_i[didx][WidWidth+:TagWidth];
            end
        end
    end

    // Extract EU Tags
    for (genvar wb = 0; wb < WritebackWidth; wb++) begin : gen_eu_tags
        assign eu_tag[wb] = eu_tag_i[wb][WidWidth+:TagWidth];
    end : gen_eu_tags

    // Combine all arbiter grants
    always_comb begin
        arb_gnts = '0;
        for (int didx = 0; didx < DispatchWidth; didx++) begin
            arb_gnts |= arb_gnt[didx];
        end
    end

    // Dispatcher per Warp
    for (genvar warp = 0; warp < NumWarps; warp++) begin : gen_dispatcher
        dispatcher #(
            .FetchWidth           ( FetchWidth            ),
            .WritebackWidth       ( WritebackWidth        ),
            .NumTags              ( NumTags               ),
            .PcWidth              ( PcWidth               ),
            .WarpWidth            ( WarpWidth             ),
            .RegIdxWidth          ( RegIdxWidth           ),
            .OperandsPerInst      ( OperandsPerInst       )
        ) i_dispatcher (
            .clk_i ( clk_i  ),
            .rst_ni( rst_ni ),

            .inorder_execution_i( inorder_execution_i ),

            .fe_handshake_i         ( fe_handshake_warp      [warp] ),
            .ib_space_available_o   ( ib_space_available_o   [warp] ),
            .ib_all_instr_finished_o( ib_all_instr_finished_o[warp] ),

            .dec_decoded_unused_ibe_i( dec_decoded_unused_ibe[warp] ),

            .disp_ready_o         ( ib_ready_warp [warp]  ),
            .dec_valid_i          ( dec_valid_warp[warp]  ),
            .dec_subwarp_id_i     ( dec_subwarp_id_i      ),
            .dec_pc_i             ( dec_pc_i              ),
            .dec_act_mask_i       ( dec_act_mask_i        ),
            .dec_valid_insts_i    ( dec_valid_insts_i     ),
            .dec_inst_i           ( dec_inst_i            ),
            .dec_dst_i            ( dec_dst_i             ),
            .dec_operands_is_reg_i( dec_operands_is_reg_i ),
            .dec_operands_i       ( dec_operands_i        ),

            .opc_ready_i           ( arb_gnts     [warp]                 ),
            .disp_valid_o          ( rr_inst_ready[0][warp]              ),
            .disp_pc_o             ( arb_in_data  [warp].pc              ),
            .disp_act_mask_o       ( arb_in_data  [warp].act_mask        ),
            .disp_tag_o            ( arb_in_data  [warp].tag             ),
            .disp_inst_o           ( arb_in_data  [warp].inst            ),
            .disp_dst_o            ( arb_in_data  [warp].dst_reg         ),
            .disp_operands_is_reg_o( arb_in_data  [warp].operands_is_reg ),
            .disp_operands_o       ( arb_in_data  [warp].operands        ),

            .opc_eu_handshake_i( opc_eu_handshake_warp[warp] ),
            .opc_eu_tag_i      ( opc_eu_tag           [warp] ),

            .eu_valid_i( eu_valid[warp] ),
            .eu_tag_i  ( eu_tag         )
        );
    end : gen_dispatcher

    // #######################################################################################
    // # Round Robin Arbiter                                                                 #
    // #######################################################################################

    for (genvar didx = 0; didx < DispatchWidth; didx++) begin : gen_rr_arb
        if (didx > 0) begin : gen_upper_rr_inst_ready
            assign rr_inst_ready[didx] = rr_inst_ready[didx-1] & (~arb_gnt[didx-1]);
        end : gen_upper_rr_inst_ready

        rr_arb_tree #(
            .DataType ( disp_data_t ),
            .NumIn    ( NumWarps    ),
            .ExtPrio  ( 1'b0 ),
            .AxiVldRdy( 1'b0 ),
            .LockIn   ( 1'b0 ),
            .FairArb  ( 1'b1 )
        ) i_rr_arb (
            .clk_i ( clk_i  ),
            .rst_ni( rst_ni ),

            .req_i  ( rr_inst_ready[didx] ),
            .gnt_o  ( arb_gnt      [didx] ),
            .data_i ( arb_in_data         ),

            // Directly to Operand Collector
            .req_o ( disp_valid_o[didx] ),
            .gnt_i ( opc_ready_i [didx] ),
            .data_o( arb_sel_data[didx] ),
            .idx_o ( arb_sel_wid [didx] ),

            // Unused
            .flush_i( 1'b0 ),
            .rr_i   ( '0   )
        );

        assign disp_tag_o            [didx] = {arb_sel_data[didx].tag, arb_sel_wid[didx]};
        assign disp_pc_o             [didx] = arb_sel_data[didx].pc;
        assign disp_act_mask_o       [didx] = arb_sel_data[didx].act_mask;
        assign disp_inst_o           [didx] = arb_sel_data[didx].inst;
        assign disp_dst_o            [didx] = arb_sel_data[didx].dst_reg;
        assign disp_operands_is_reg_o[didx] = arb_sel_data[didx].operands_is_reg;
        assign disp_operands_o       [didx] = arb_sel_data[didx].operands;
    end : gen_rr_arb

    // #######################################################################################
    // # Assertions                                                                          #
    // #######################################################################################

    `ifndef SYNTHESIS
        for (genvar didx = 0; didx < DispatchWidth; didx++) begin : gen_out_asserts
            for (genvar other_didx = 0; other_didx < DispatchWidth; other_didx++)
            begin : gen_out_asserts_inner
                if (didx != other_didx) begin : gen_diff_didx
                    // Check for OPC EU Handshake for the same warp received on multiple dispatch outputs
                    assert property (@(posedge clk_i) disable iff (!rst_ni)
                        (opc_eu_handshake_i[didx] && opc_eu_handshake_i[other_didx]
                        -> opc_eu_tag_i[didx][WidWidth-1:0]
                            != opc_eu_tag_i[other_didx][WidWidth-1:0]))
                    else $error("OPC EU Handshake for the same warp received!");

                    // Check that no two dispatch outputs dispatch to the same warp in the same cycle
                    assert property (@(posedge clk_i) disable iff (!rst_ni)
                        (disp_valid_o[didx] && opc_ready_i[didx] && disp_valid_o[other_didx] && opc_ready_i[other_didx]
                        -> arb_gnt[didx] != arb_gnt[other_didx]))
                    else $error("Two outputs dispatching to the same warp in the same cycle!");
                end : gen_diff_didx
            end : gen_out_asserts_inner
        end : gen_out_asserts
    `endif // SYNTHESIS

endmodule : multi_warp_dispatcher
