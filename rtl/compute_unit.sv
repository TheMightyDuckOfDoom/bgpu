// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Compute Unit
module compute_unit #(
    /// Number of inflight instructions per warp
    parameter int unsigned NumTags = 8,
    /// Width of the Program Counter
    parameter int unsigned PcWidth = 16,
    /// Number of warps
    parameter int unsigned NumWarps = 8,
    /// Number of threads per warp
    parameter int unsigned WarpWidth = 4,
    /// Encoded instruction width
    parameter int unsigned EncInstWidth = 32,
    /// How many instructions that wait on previous results can be buffered per warp
    parameter int unsigned WaitBufferSizePerWarp = 4,
    /// How many registers can each warp access as operand or destination
    parameter int unsigned RegIdxWidth = 8,
    /// How many operands each instruction can have
    parameter int unsigned OperandsPerInst = 2,
    /// How many register banks are available
    parameter int unsigned NumBanks = 4,
    /// How many operand collectors are available
    parameter int unsigned NumOperandCollectors = 6,
    /// Should the register banks be dual ported?
    parameter bit          DualPortRegisterBanks = 1'b0,
    /// Width of the registers
    parameter int unsigned RegWidth = 32,

    /// Dependent parameter, do **not** overwrite.
    parameter int unsigned TagWidth = $clog2(NumTags),
    parameter int unsigned WidWidth = NumWarps > 1 ? $clog2(NumWarps) : 1,
    parameter type reg_idx_t = logic [RegIdxWidth-1:0],
    parameter type iid_t = logic [WidWidth+TagWidth-1:0],
    parameter type pc_t = logic [PcWidth-1:0],
    parameter type act_mask_t = logic [WarpWidth-1:0],
    parameter type warp_data_t = logic [RegWidth * WarpWidth-1:0]
) (
    // Clock and reset
    input logic clk_i,
    input logic rst_ni,

    input logic set_ready_i,
    output [NumWarps-1:0] warp_active_o,
    output [NumWarps-1:0] warp_stopped_o,

    // Dummy inputs / outputs
    input  logic                    ic_write_i,
    input  logic [PcWidth-1:0]      ic_write_pc_i,
    input  logic [EncInstWidth-1:0] ic_write_inst_i,

    output logic       eu_to_opc_ready_o,
    output logic       opc_to_eu_valid_o,
    output iid_t       opc_to_eu_tag_o,
    output pc_t        opc_to_eu_pc_o,
    output act_mask_t  opc_to_eu_act_mask_o,
    output reg_idx_t   opc_to_eu_dst_o,
    output warp_data_t [OperandsPerInst-1:0] opc_to_eu_operands_o,

    output logic       opc_to_eu_ready_o,
    output logic       eu_to_opc_valid_o,
    output iid_t       eu_to_opc_tag_o,
    output reg_idx_t   eu_to_opc_dst_o,
    output warp_data_t eu_to_opc_data_o
);
    // #######################################################################################
    // # Typedefs                                                                            #
    // #######################################################################################

    // Typedefs
    typedef logic [    WidWidth-1:0] wid_t;
    typedef logic [EncInstWidth-1:0] enc_inst_t;

    typedef struct packed {
        reg_idx_t dst;
        reg_idx_t [OperandsPerInst-1:0] src;
    } dec_inst_t;

    // Fetcher to Instruction Cache type
    typedef struct packed {
        pc_t pc;
        act_mask_t act_mask;
        wid_t warp_id;
    } fe_to_ic_data_t;

    // Instruction Cache to Decoder type
    typedef struct packed {
        pc_t pc;
        act_mask_t act_mask;
        wid_t warp_id;
        enc_inst_t inst;
    } ic_to_dec_data_t;

    // Decoder to Instruction Buffer type
    typedef struct packed {
        pc_t pc;
        act_mask_t act_mask;
        wid_t warp_id;
        dec_inst_t inst;
    } dec_to_ib_data_t;

    // Multi Warp Dispatcher to Register Operand Collector Stage type
    typedef struct packed {
        iid_t tag;
        pc_t pc;
        act_mask_t act_mask;
        reg_idx_t dst;
        reg_idx_t [OperandsPerInst-1:0] operands;
    } disp_to_opc_data_t;

    // Register Operand Collector Stage to Execution Units type
    typedef struct packed {
        iid_t tag;
        pc_t pc;
        act_mask_t act_mask;
        reg_idx_t dst;
        warp_data_t [OperandsPerInst-1:0] operands;
    } opc_to_eu_data_t;

    // Execution Units to Register Operand Collector Stage type
    typedef struct packed {
        iid_t tag;
        reg_idx_t dst;
        warp_data_t data;
    } eu_to_opc_data_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################


    // Fetcher to Instruction Cache
    logic fe_to_ic_valid_d, fe_to_ic_valid_q;
    logic ic_to_fe_ready_d, ic_to_fe_ready_q;
    fe_to_ic_data_t fe_to_ic_data_d, fe_to_ic_data_q;

    /// Instruction Cache to Decoder
    logic ic_to_dec_valid_d, ic_to_dec_valid_q;
    logic dec_to_ic_ready_d, dec_to_ic_ready_q;
    ic_to_dec_data_t ic_to_dec_data_d, ic_to_dec_data_q;

    // Decoder to Fetcher
    logic dec_to_fetch_decoded;
    logic dec_to_fetch_stop_warp;
    wid_t dec_to_fetch_decoded_warp_id;
    pc_t  dec_to_fetch_decoded_next_pc;

    // Decoder to Instruction Buffer
    logic dec_to_ib_valid_d, dec_to_ib_valid_q;
    logic ib_to_dec_ready_d, ib_to_dec_ready_q;
    dec_to_ib_data_t dec_to_ib_data_d, dec_to_ib_data_q;

    // Instruction Buffer to Fetcher
    logic [NumWarps-1:0] ib_space_available; // Which warp has space for a new instruction?

    // Multi Warp Dispatcher to Register Operand Collector Stage
    logic disp_to_opc_valid, opc_to_disp_ready;
    disp_to_opc_data_t disp_to_opc_data;

    // Register Operand Collector Stage to Execution Units
    logic opc_to_eu_valid, opc_to_eu_ready;
    opc_to_eu_data_t opc_to_eu_data;

    // Execution Units to Register Operand Collector Stage
    logic eu_to_opc_valid, eu_to_opc_ready;
    eu_to_opc_data_t eu_to_opc_data;

    // #######################################################################################
    // # Fetcher                                                                             #
    // #######################################################################################

    fetcher #(
        .PcWidth  ( PcWidth   ),
        .NumWarps ( NumWarps  ),
        .WarpWidth( WarpWidth )
    ) i_fetcher (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .set_ready_i   ( set_ready_i    ),
        .warp_active_o ( warp_active_o  ),
        .warp_stopped_o( warp_stopped_o ),

        .ib_space_available_i( ib_space_available ),

        .ic_ready_i   ( ic_to_fe_ready_q         ),
        .fe_valid_o   ( fe_to_ic_valid_d         ),
        .fe_pc_o      ( fe_to_ic_data_d.pc       ),
        .fe_act_mask_o( fe_to_ic_data_d.act_mask ),
        .fe_warp_id_o ( fe_to_ic_data_d.warp_id  ),

        .dec_decoded_i         ( dec_to_fetch_decoded         ),
        .dec_stop_warp_i       ( dec_to_fetch_stop_warp       ),
        .dec_decoded_warp_id_i ( dec_to_fetch_decoded_warp_id ),
        .dec_decoded_next_pc_i ( dec_to_fetch_decoded_next_pc )
    );

    // #######################################################################################
    // # Fetcher to Instruction Cache - Register                                             #
    // #######################################################################################

    stream_register #(
        .T( fe_to_ic_data_t )
    ) i_fe_to_ic_reg (
        .clk_i     ( clk_i  ),
        .rst_ni    ( rst_ni ),
        .clr_i     ( 1'b0   ),
        .testmode_i( 1'b0   ),

        .valid_i( fe_to_ic_valid_d ),
        .ready_o( ic_to_fe_ready_q ),
        .data_i ( fe_to_ic_data_d  ),

        .valid_o( fe_to_ic_valid_q ),
        .ready_i( ic_to_fe_ready_d ),
        .data_o ( fe_to_ic_data_q  )
    );

    // #######################################################################################
    // # Instruction Cache                                                                   #
    // #######################################################################################

    dummy_instruction_cache #(
        .MemorySize  ( 32        ),
        .PcWidth     ( PcWidth   ),
        .NumWarps    ( NumWarps  ),
        .WarpWidth   ( WarpWidth ),
        .EncInstWidth( 32        )
    ) i_instruction_cache (
        .clk_i        ( clk_i           ),
        .mem_write_i  ( ic_write_i      ),
        .mem_pc_i     ( ic_write_pc_i   ),
        .mem_inst_i   ( ic_write_inst_i ),

        .ic_ready_o   ( ic_to_fe_ready_d         ),
        .fe_valid_i   ( fe_to_ic_valid_q         ),
        .fe_pc_i      ( fe_to_ic_data_q.pc       ),
        .fe_act_mask_i( fe_to_ic_data_q.act_mask ),
        .fe_warp_id_i ( fe_to_ic_data_q.warp_id  ),

        .dec_ready_i  ( dec_to_ic_ready_q         ),
        .ic_valid_o   ( ic_to_dec_valid_d         ),
        .ic_pc_o      ( ic_to_dec_data_d.pc       ),
        .ic_act_mask_o( ic_to_dec_data_d.act_mask ),
        .ic_warp_id_o ( ic_to_dec_data_d.warp_id  ),
        .ic_inst_o    ( ic_to_dec_data_d.inst     )
    );

    // #######################################################################################
    // # Instruction Cache to Decoder - Register                                             #
    // #######################################################################################

    stream_register #(
        .T( ic_to_dec_data_t )
    ) i_ic_to_dec_reg (
        .clk_i     ( clk_i  ),
        .rst_ni    ( rst_ni ),
        .clr_i     ( 1'b0   ),
        .testmode_i( 1'b0   ),

        .valid_i( ic_to_dec_valid_d ),
        .ready_o( dec_to_ic_ready_q ),
        .data_i ( ic_to_dec_data_d  ),

        .valid_o( ic_to_dec_valid_q ),
        .ready_i( dec_to_ic_ready_d ),
        .data_o ( ic_to_dec_data_q  )
    );

    // #######################################################################################
    // # Instruction Decoder                                                                 #
    // #######################################################################################

    decoder #(
        .PcWidth     ( PcWidth      ),
        .NumWarps    ( NumWarps     ),
        .WarpWidth   ( WarpWidth    ),
        .EncInstWidth( EncInstWidth ),
        .dec_inst_t  ( dec_inst_t   )
    ) i_decoder (
        .dec_ready_o  ( dec_to_ic_ready_d         ),
        .ic_valid_i   ( ic_to_dec_valid_q         ),
        .ic_pc_i      ( ic_to_dec_data_q.pc       ),
        .ic_act_mask_i( ic_to_dec_data_q.act_mask ),
        .ic_warp_id_i ( ic_to_dec_data_q.warp_id  ),
        .ic_inst_i    ( ic_to_dec_data_q.inst     ),

        .disp_ready_i  ( ib_to_dec_ready_q         ),
        .dec_valid_o   ( dec_to_ib_valid_d         ),
        .dec_pc_o      ( dec_to_ib_data_d.pc       ),
        .dec_act_mask_o( dec_to_ib_data_d.act_mask ),
        .dec_warp_id_o ( dec_to_ib_data_d.warp_id  ),
        .dec_inst_o    ( dec_to_ib_data_d.inst     ),

        .dec_decoded_o         ( dec_to_fetch_decoded         ),
        .dec_stop_warp_o       ( dec_to_fetch_stop_warp       ),
        .dec_decoded_warp_id_o ( dec_to_fetch_decoded_warp_id ),
        .dec_decoded_next_pc_o ( dec_to_fetch_decoded_next_pc )
    );

    // #######################################################################################
    // # Decoder to Instruction Buffer - Register                                            #
    // #######################################################################################

    stream_register #(
        .T( dec_to_ib_data_t )
    ) i_dec_to_ib_reg (
        .clk_i     ( clk_i  ),
        .rst_ni    ( rst_ni ),
        .clr_i     ( 1'b0   ),
        .testmode_i( 1'b0   ),

        .valid_i( dec_to_ib_valid_d ),
        .ready_o( ib_to_dec_ready_q ),
        .data_i ( dec_to_ib_data_d  ),

        .valid_o( dec_to_ib_valid_q ),
        .ready_i( ib_to_dec_ready_d ),
        .data_o ( dec_to_ib_data_q  )
    );

    // #######################################################################################
    // # Multi Warp Dispatcher                                                               #
    // #######################################################################################

    multi_warp_dispatcher #(
        .NumTags              ( NumTags               ),
        .PcWidth              ( PcWidth               ),
        .NumWarps             ( NumWarps              ),
        .WarpWidth            ( WarpWidth             ),
        .WaitBufferSizePerWarp( WaitBufferSizePerWarp ),
        .RegIdxWidth          ( RegIdxWidth           ),
        .OperandsPerInst      ( OperandsPerInst       ),
        .dec_inst_t           ( dec_inst_t            )
    ) i_warp_dispatcher (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .fe_handshake_i( fe_to_ic_valid_d && ic_to_fe_ready_q ),
        .fe_warp_id_i  ( fe_to_ic_data_d.warp_id              ),

        .ib_space_available_o( ib_space_available ),

        .ib_ready_o    ( ib_to_dec_ready_d         ),
        .dec_valid_i   ( dec_to_ib_valid_q         ),
        .dec_pc_i      ( dec_to_ib_data_q.pc       ),
        .dec_act_mask_i( dec_to_ib_data_q.act_mask ),
        .dec_warp_id_i ( dec_to_ib_data_q.warp_id  ),
        .dec_inst_i    ( dec_to_ib_data_q.inst     ),

        .opc_ready_i    ( opc_to_disp_ready         ),
        .disp_valid_o   ( disp_to_opc_valid         ),
        .disp_tag_o     ( disp_to_opc_data.tag      ),
        .disp_pc_o      ( disp_to_opc_data.pc       ),
        .disp_act_mask_o( disp_to_opc_data.act_mask ),
        .disp_dst_o     ( disp_to_opc_data.dst      ),
        .disp_operands_o( disp_to_opc_data.operands ),

        .eu_valid_i( eu_to_opc_valid && opc_to_eu_ready ),
        .eu_tag_i  ( eu_to_opc_data.tag                 )
    );

    // #######################################################################################
    // # Register Operand Collector Stage                                                    #
    // #######################################################################################

    register_opc_stage #(
        .NumTags              ( NumTags               ),
        .PcWidth              ( PcWidth               ),
        .NumWarps             ( NumWarps              ),
        .WarpWidth            ( WarpWidth             ),
        .RegIdxWidth          ( RegIdxWidth           ),
        .OperandsPerInst      ( OperandsPerInst       ),
        .NumBanks             ( NumBanks              ),
        .RegWidth             ( RegWidth              ),
        .DualPortRegisterBanks( DualPortRegisterBanks ),
        .NumOperandCollectors ( NumOperandCollectors  )
    ) i_register_opc_stage (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .opc_ready_o    ( opc_to_disp_ready         ),
        .disp_valid_i   ( disp_to_opc_valid         ),
        .disp_tag_i     ( disp_to_opc_data.tag      ),
        .disp_pc_i      ( disp_to_opc_data.pc       ),
        .disp_act_mask_i( disp_to_opc_data.act_mask ),
        .disp_dst_i     ( disp_to_opc_data.dst      ),
        .disp_src_i     ( disp_to_opc_data.operands ),

        .eu_ready_i        ( eu_to_opc_ready         ),
        .opc_valid_o       ( opc_to_eu_valid         ),
        .opc_tag_o         ( opc_to_eu_data.tag      ),
        .opc_pc_o          ( opc_to_eu_data.pc       ),
        .opc_act_mask_o    ( opc_to_eu_data.act_mask ),
        .opc_dst_o         ( opc_to_eu_data.dst      ),
        .opc_operand_data_o( opc_to_eu_data.operands ),

        .opc_to_eu_ready_o( opc_to_eu_ready     ),
        .eu_valid_i       ( eu_to_opc_valid     ),
        .eu_tag_i         ( eu_to_opc_data.tag  ),
        .eu_dst_i         ( eu_to_opc_data.dst  ),
        .eu_data_i        ( eu_to_opc_data.data )
    );

    // #######################################################################################
    // # Execution Units                                                                     #
    // #######################################################################################

    // Integer Unit
    integer_unit #(
        .RegWidth       ( RegWidth        ),
        .WarpWidth      ( WarpWidth       ),
        .OperandsPerInst( OperandsPerInst ),
        .iid_t          ( iid_t           ),
        .reg_idx_t      ( reg_idx_t       )
    ) i_integer_unit (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .eu_to_opc_ready_o   ( eu_to_opc_ready         ),
        .opc_to_eu_valid_i   ( opc_to_eu_valid         ),
        .opc_to_eu_tag_i     ( opc_to_eu_data.tag      ),
        .opc_to_eu_dst_i     ( opc_to_eu_data.dst      ),
        .opc_to_eu_operands_i( opc_to_eu_data.operands ),

        .rc_to_eu_ready_i( opc_to_eu_ready     ),
        .eu_to_rc_valid_o( eu_to_opc_valid     ),
        .eu_to_rc_tag_o  ( eu_to_opc_data.tag  ),
        .eu_to_rc_dst_o  ( eu_to_opc_data.dst  ),
        .eu_to_rc_data_o ( eu_to_opc_data.data )
    );

    // #######################################################################################
    // # Dummy Outputs                                                                       #
    // #######################################################################################

    assign eu_to_opc_ready_o    = eu_to_opc_ready;
    assign opc_to_eu_valid_o    = opc_to_eu_valid;
    assign opc_to_eu_tag_o      = opc_to_eu_data.tag;
    assign opc_to_eu_pc_o       = opc_to_eu_data.pc;
    assign opc_to_eu_act_mask_o = opc_to_eu_data.act_mask;
    assign opc_to_eu_dst_o      = opc_to_eu_data.dst;
    assign opc_to_eu_operands_o = opc_to_eu_data.operands;

    assign opc_to_eu_ready_o = opc_to_eu_ready;
    assign eu_to_opc_valid_o = eu_to_opc_valid;
    assign eu_to_opc_tag_o   = eu_to_opc_data.tag;
    assign eu_to_opc_dst_o   = eu_to_opc_data.dst;
    assign eu_to_opc_data_o  = eu_to_opc_data.data;

endmodule : compute_unit
