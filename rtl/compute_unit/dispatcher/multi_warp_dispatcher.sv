// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Multi Warp Dispatcher
/// Contains a dispatcher per warp
module multi_warp_dispatcher import bgpu_pkg::*; #(
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
    parameter type         wid_t          = logic [         WidWidth-1:0],
    parameter type         reg_idx_t      = logic [      RegIdxWidth-1:0],
    parameter type         pc_t           = logic [          PcWidth-1:0],
    parameter type         act_mask_t     = logic [        WarpWidth-1:0],
    parameter type         tag_t          = logic [         TagWidth-1:0],
    parameter type         iid_t          = logic [TagWidth+WidWidth-1:0],
    parameter type         subwarp_id_t   = logic [   SubwarpIdWidth-1:0]
) (
    /// Clock and Reset
    input  logic clk_i,
    input  logic rst_ni,

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
    output logic        ib_ready_o,
    input  logic        dec_valid_i,
    input  pc_t         dec_pc_i,
    input  act_mask_t   dec_act_mask_i,
    input  wid_t        dec_warp_id_i,
    input  subwarp_id_t dec_subwarp_id_i,
    input  inst_t       dec_inst_i,
    input  reg_idx_t    dec_dst_i,
    input  logic        [OperandsPerInst-1:0] dec_operands_required_i,
    input  reg_idx_t    [OperandsPerInst-1:0] dec_operands_i,

    /// To Operand Collector
    input  logic      opc_ready_i,
    output logic      disp_valid_o,
    output iid_t      disp_tag_o,
    output pc_t       disp_pc_o,
    output act_mask_t disp_act_mask_o,
    output inst_t     disp_inst_o,
    output reg_idx_t  disp_dst_o,
    output logic      [OperandsPerInst-1:0] disp_operands_required_o,
    output reg_idx_t  [OperandsPerInst-1:0] disp_operands_o,

    /// From Execution Units
    input  logic eu_valid_i,
    input  iid_t eu_tag_i
);
    // #######################################################################################
    // # Typedefs                                                                            #
    // #######################################################################################

    typedef struct packed {
        tag_t       tag;
        pc_t        pc;
        act_mask_t  act_mask;
        inst_t      inst;
        reg_idx_t   dst_reg;
        logic       [OperandsPerInst-1:0] operands_required;
        reg_idx_t   [OperandsPerInst-1:0] operands;
    } disp_data_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Dispatcher per warp
    logic [NumWarps-1:0] dec_valid_warp, ib_ready_warp, fe_handshake_warp;

    logic [NumWarps-1:0] eu_valid;

    // Round Robin Arbiter
    logic [NumWarps-1:0] arb_gnt;
    logic [NumWarps-1:0] rr_inst_ready;

    wid_t arb_sel_wid;
    disp_data_t [NumWarps-1:0] arb_in_data;
    disp_data_t arb_sel_data;

    // Control decoded Demultiplexer
    logic [NumWarps-1:0] dec_control_decoded_warp;

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
        eu_valid[eu_tag_i[WidWidth-1:0]] = eu_valid_i;
    end

    // Control Decoded Demultiplexer
    always_comb begin
        dec_control_decoded_warp = '0;
        dec_control_decoded_warp[dec_control_decoded_warp_id_i] = dec_control_decoded_i;
    end

    // Dispatcher per Warp
    for (genvar warp = 0; warp < NumWarps; warp++) begin : gen_dispatcher
        dispatcher #(
            .NumTags              ( NumTags               ),
            .PcWidth              ( PcWidth               ),
            .WarpWidth            ( WarpWidth             ),
            .WaitBufferSizePerWarp( WaitBufferSizePerWarp ),
            .RegIdxWidth          ( RegIdxWidth           ),
            .OperandsPerInst      ( OperandsPerInst       )
        ) i_dispatcher (
            .clk_i ( clk_i  ),
            .rst_ni( rst_ni ),

            .fe_handshake_i         ( fe_handshake_warp      [warp] ),
            .ib_space_available_o   ( ib_space_available_o   [warp] ),
            .ib_all_instr_finished_o( ib_all_instr_finished_o[warp] ),

            .dec_control_decoded_i( dec_control_decoded_warp[warp] ),

            .disp_ready_o           ( ib_ready_warp [warp]    ),
            .dec_valid_i            ( dec_valid_warp[warp]    ),
            .dec_subwarp_id_i       ( dec_subwarp_id_i        ),
            .dec_pc_i               ( dec_pc_i                ),
            .dec_act_mask_i         ( dec_act_mask_i          ),
            .dec_inst_i             ( dec_inst_i              ),
            .dec_dst_i              ( dec_dst_i               ),
            .dec_operands_required_i( dec_operands_required_i ),
            .dec_operands_i         ( dec_operands_i          ),

            .opc_ready_i             ( arb_gnt      [warp]                   ),
            .disp_valid_o            ( rr_inst_ready[warp]                   ),
            .disp_pc_o               ( arb_in_data  [warp].pc                ),
            .disp_act_mask_o         ( arb_in_data  [warp].act_mask          ),
            .disp_tag_o              ( arb_in_data  [warp].tag               ),
            .disp_inst_o             ( arb_in_data  [warp].inst              ),
            .disp_dst_o              ( arb_in_data  [warp].dst_reg           ),
            .disp_operands_required_o( arb_in_data  [warp].operands_required ),
            .disp_operands_o         ( arb_in_data  [warp].operands          ),

            .eu_valid_i( eu_valid[warp]         ),
            .eu_tag_i  ( eu_tag_i[WidWidth+:TagWidth] )
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

    assign disp_tag_o               = {arb_sel_data.tag, arb_sel_wid};
    assign disp_pc_o                = arb_sel_data.pc;
    assign disp_act_mask_o          = arb_sel_data.act_mask;
    assign disp_inst_o              = arb_sel_data.inst;
    assign disp_dst_o               = arb_sel_data.dst_reg;
    assign disp_operands_required_o = arb_sel_data.operands_required;
    assign disp_operands_o          = arb_sel_data.operands;

endmodule : multi_warp_dispatcher
