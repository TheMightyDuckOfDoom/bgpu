// Copyright March 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Multi Warp Dispatcher
/// Contains a dispatcher per warp
module multi_warp_dispatcher #(
    /// Number of inflight instructions per warp
    parameter int NumTags = 8,
    /// Width of the Program Counter
    parameter int PcWidth = 32,
    /// Number of warps per compute unit
    parameter int NumWarps = 8,
    /// Number of threads per warp
    parameter int WarpWidth = 32,
    /// How many instructions that wait on previous results can be buffered per warp
    parameter int WaitBufferSizePerWarp = 4,
    /// How many registers can each warp access as operand or destination
    parameter int RegIdxWidth = 6,
    /// How many operands each instruction can have
    parameter int OperandsPerInst = 2,

    parameter type dec_inst_t = logic,

    /// Dependent parameter, do **not** overwrite.
    parameter int  TagWidth   = $clog2(NumTags),
    parameter int  WidWidth   = $clog2(NumWarps),
    parameter type wid_t      = logic [   WidWidth-1:0],
    parameter type reg_idx_t  = logic [RegIdxWidth-1:0],
    parameter type pc_t       = logic [    PcWidth-1:0],
    parameter type act_mask_t = logic [  WarpWidth-1:0],
    parameter type tag_t      = logic [   TagWidth-1:0],
    parameter type iid_t      = logic [TagWidth+WidWidth-1:0]
) (
    /// Clock and Reset
    input  logic clk_i,
    input  logic rst_ni,

    /// From fetcher -> which warp gets fetched next
    input  logic fe_handshake_i,
    input  wid_t fe_warp_id_i,

    /// To fetcher -> which warps have space for a new instruction?
    output logic [NumWarps-1:0] ib_space_available_o,

    /// From decoder
    output logic      ib_ready_o,
    input  logic      dec_valid_i,
    input  pc_t       dec_pc_i,
    input  act_mask_t dec_act_mask_i,
    input  wid_t      dec_warp_id_i,
    input  dec_inst_t dec_inst_i,

    /// To Operand Collector
    input  logic     opc_ready_i,
    output logic     disp_valid_o,
    output iid_t     disp_tag_o,
    output reg_idx_t disp_dst_o,
    output reg_idx_t [OperandsPerInst-1:0] disp_operands_o,

    /// From Execution Units
    input  logic eu_valid_i,
    input  iid_t eu_tag_i
);
    // #######################################################################################
    // # Typedefs                                                                            #
    // #######################################################################################

    typedef struct packed {
        tag_t tag;
        reg_idx_t dst_reg;
        reg_idx_t [OperandsPerInst-1:0] operands;
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

    // #######################################################################################
    // # Dispatcher per warp                                                                 #
    // #######################################################################################

    always_comb begin
        dec_valid_warp = '0;
        dec_valid_warp[dec_warp_id_i] = dec_valid_i;

        ib_ready_o  = '0;
        ib_ready_o = ib_ready_warp[dec_warp_id_i];
    end

    always_comb begin
        fe_handshake_warp = '0;
        fe_handshake_warp[fe_warp_id_i] = fe_handshake_i;
    end

    always_comb begin
        eu_valid = '0;
        eu_valid[eu_tag_i[WidWidth+TagWidth-1:TagWidth]] = eu_valid_i;
    end

    for(genvar warp = 0; warp < NumWarps; warp++) begin : gen_dispatcher
        dispatcher #(
            .NumTags              ( NumTags               ),
            .PcWidth              ( PcWidth               ),
            .WarpWidth            ( WarpWidth             ),
            .WaitBufferSizePerWarp( WaitBufferSizePerWarp ),
            .RegIdxWidth          ( RegIdxWidth           ),
            .OperandsPerInst      ( OperandsPerInst       ),
            .dec_inst_t           ( dec_inst_t            )
        ) i_dispatcher (
            .clk_i ( clk_i  ),
            .rst_ni( rst_ni ),

            .fe_handshake_i      ( fe_handshake_warp[warp]    ),
            .ib_space_available_o( ib_space_available_o[warp] ),

            .disp_ready_o  ( ib_ready_warp[warp]  ),
            .dec_valid_i   ( dec_valid_warp[warp] ),
            .dec_pc_i      ( dec_pc_i             ),
            .dec_act_mask_i( dec_act_mask_i       ),
            .dec_inst_i    ( dec_inst_i           ),
        
            .opc_ready_i    ( arb_gnt      [warp]        ),
            .disp_valid_o   ( rr_inst_ready[warp]        ),
            .disp_tag_o     ( arb_in_data[warp].tag      ),
            .disp_dst_o     ( arb_in_data[warp].dst_reg  ),
            .disp_operands_o( arb_in_data[warp].operands ),

            .eu_valid_i( eu_valid[warp]         ),
            .eu_tag_i  ( eu_tag_i[TagWidth-1:0] )
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

    assign disp_tag_o      = {arb_sel_wid, arb_sel_data.tag};
    assign disp_dst_o      = arb_sel_data.dst_reg;
    assign disp_operands_o = arb_sel_data.operands;

endmodule : multi_warp_dispatcher
