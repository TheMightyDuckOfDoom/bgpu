// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Multi Warp Dispatcher
/// Contains a dispatcher per warp
module multi_warp_dispatcher import bgpu_pkg::*; #(
    /// Number of instructions to fetch for the warp
    parameter int unsigned FetchWidth = 1,
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
    /// How many instructions that wait on previous results can be buffered per warp
    parameter int unsigned WaitBufferSizePerWarp = 4,
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
    output logic [NumWarps-1:0] ib_space_available_o,
    // Are there any instructions in flight?
    output logic [NumWarps-1:0] ib_all_instr_finished_o,

    /// From decoder -> control decoded
    input  logic dec_control_decoded_i,
    input  wid_t dec_control_decoded_warp_id_i,

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
    input  logic        opc_ready_i,
    output logic        disp_valid_o,
    output iid_t        disp_tag_o,
    output pc_t         disp_pc_o,
    output act_mask_t   disp_act_mask_o,
    output inst_t       disp_inst_o,
    output reg_idx_t    disp_dst_o,
    output op_is_reg_t  disp_operands_is_reg_o,
    output op_reg_idx_t disp_operands_o,

    /// From Operand Collector -> instruction has read its operands
    input logic opc_eu_handshake_i,
    input iid_t opc_eu_tag_i,

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
    warp_mask_t arb_gnt;
    warp_mask_t rr_inst_ready;

    wid_t arb_sel_wid;
    disp_data_t [NumWarps-1:0] arb_in_data;
    disp_data_t arb_sel_data;

    // Control decoded Demultiplexer
    warp_mask_t dec_control_decoded_warp;

    // OPC EU Handshake Demultiplexer
    warp_mask_t opc_eu_handshake_warp;

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
        for (int warp = 0; warp < NumWarps; warp++) 
            for (int wb = 0; wb < WritebackWidth; wb++) 
                eu_valid[warp][wb] = eu_valid_i[wb] && (eu_tag_i[wb][WidWidth-1:0] == warp[WidWidth-1:0]);
    end

    // Control Decoded Demultiplexer
    always_comb begin
        dec_control_decoded_warp = '0;
        dec_control_decoded_warp[dec_control_decoded_warp_id_i] = dec_control_decoded_i;
    end

    // OPC EU Handshake Demultiplexer
    always_comb begin
        opc_eu_handshake_warp = '0;
        opc_eu_handshake_warp[opc_eu_tag_i[WidWidth-1:0]] = opc_eu_handshake_i;
    end

    // Extract EU Tags
    for (genvar wb = 0; wb < WritebackWidth; wb++) begin : gen_eu_tags
        assign eu_tag[wb] = eu_tag_i[wb][WidWidth+:TagWidth];
    end : gen_eu_tags

    // Dispatcher per Warp
    for (genvar warp = 0; warp < NumWarps; warp++) begin : gen_dispatcher
        dispatcher #(
            .FetchWidth           ( FetchWidth            ),
            .WritebackWidth       ( WritebackWidth        ),
            .NumTags              ( NumTags               ),
            .PcWidth              ( PcWidth               ),
            .WarpWidth            ( WarpWidth             ),
            .WaitBufferSizePerWarp( WaitBufferSizePerWarp ),
            .RegIdxWidth          ( RegIdxWidth           ),
            .OperandsPerInst      ( OperandsPerInst       )
        ) i_dispatcher (
            .clk_i ( clk_i  ),
            .rst_ni( rst_ni ),

            .inorder_execution_i( inorder_execution_i ),

            .fe_handshake_i         ( fe_handshake_warp      [warp] ),
            .ib_space_available_o   ( ib_space_available_o   [warp] ),
            .ib_all_instr_finished_o( ib_all_instr_finished_o[warp] ),

            .dec_control_decoded_i( dec_control_decoded_warp[warp] ),

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

            .opc_ready_i           ( arb_gnt      [warp]                 ),
            .disp_valid_o          ( rr_inst_ready[warp]                 ),
            .disp_pc_o             ( arb_in_data  [warp].pc              ),
            .disp_act_mask_o       ( arb_in_data  [warp].act_mask        ),
            .disp_tag_o            ( arb_in_data  [warp].tag             ),
            .disp_inst_o           ( arb_in_data  [warp].inst            ),
            .disp_dst_o            ( arb_in_data  [warp].dst_reg         ),
            .disp_operands_is_reg_o( arb_in_data  [warp].operands_is_reg ),
            .disp_operands_o       ( arb_in_data  [warp].operands        ),

            .opc_eu_handshake_i( opc_eu_handshake_warp[warp]      ),
            .opc_eu_tag_i      ( opc_eu_tag_i[WidWidth+:TagWidth] ),

            .eu_valid_i( eu_valid[warp] ),
            .eu_tag_i  ( eu_tag         )
        );
    end : gen_dispatcher

    // #######################################################################################
    // # Round Robin Arbiter                                                                 #
    // #######################################################################################

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

        .req_i  ( rr_inst_ready ),
        .gnt_o  ( arb_gnt       ),
        .data_i ( arb_in_data   ),

        // Directly to Operand Collector
        .req_o ( disp_valid_o ),
        .gnt_i ( opc_ready_i  ),
        .data_o( arb_sel_data ),
        .idx_o ( arb_sel_wid  ),

        // Unused
        .flush_i( 1'b0 ),
        .rr_i   ( '0   )
    );

    assign disp_tag_o             = {arb_sel_data.tag, arb_sel_wid};
    assign disp_pc_o              = arb_sel_data.pc;
    assign disp_act_mask_o        = arb_sel_data.act_mask;
    assign disp_inst_o            = arb_sel_data.inst;
    assign disp_dst_o             = arb_sel_data.dst_reg;
    assign disp_operands_is_reg_o = arb_sel_data.operands_is_reg;
    assign disp_operands_o        = arb_sel_data.operands;

endmodule : multi_warp_dispatcher
