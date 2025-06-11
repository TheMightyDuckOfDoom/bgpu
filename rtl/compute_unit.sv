// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "bgpu/instructions.svh"

/// Compute Unit
module compute_unit #(
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
    /// Number of inflight instructions per warp
    parameter int unsigned NumTags = WaitBufferSizePerWarp * 2,
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
    // Memory Address width in bits
    parameter int unsigned AddressWidth = 32,
    // Memory Block size in bytes -> Memory request width
    parameter int unsigned BlockIdxBits = 4,
    // Width of the id for requests queue
    parameter int unsigned OutstandingReqIdxWidth = 3,

    /// Dependent parameter, do **not** overwrite.
    parameter int unsigned BlockAddrWidth  = AddressWidth - BlockIdxBits,
    parameter int unsigned BlockWidth      = 1 << BlockIdxBits, // In bytes
    parameter int unsigned ThreadIdxWidth  = WarpWidth > 1 ? $clog2(WarpWidth) : 1,
    parameter type pc_t         = logic  [             PcWidth-1:0],
    parameter type block_addr_t = logic  [      BlockAddrWidth-1:0],
    parameter type byte_t       = logic  [                     7:0],
    parameter type block_data_t = byte_t [          BlockWidth-1:0],
    parameter type block_idx_t  = logic  [        BlockIdxBits-1:0],
    parameter type block_mask_t = logic  [          BlockWidth-1:0],
    parameter type req_id_t     = logic  [OutstandingReqIdxWidth + ThreadIdxWidth-1:0]
) (
    // Clock and reset
    input logic clk_i,
    input logic rst_ni,

    input logic set_ready_i,
    output [NumWarps-1:0] warp_active_o,
    output [NumWarps-1:0] warp_stopped_o,

    // Dummy inputs / outputs
    input  logic                    ic_write_i,
    input  pc_t      ic_write_pc_i,
    input  logic [EncInstWidth-1:0] ic_write_inst_i,

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
    input  block_data_t mem_rsp_data_i
);
    // #######################################################################################
    // # Local Parameters                                                                    #
    // #######################################################################################

    localparam int unsigned WidWidth = NumWarps > 1 ? $clog2(NumWarps) : 1;
    localparam int unsigned TagWidth = NumTags  > 1 ? $clog2( NumTags) : 1;

    // #######################################################################################
    // # Typedefs                                                                            #
    // #######################################################################################

    // Typedefs
    typedef logic [         RegIdxWidth-1:0] reg_idx_t;
    typedef logic [ WidWidth + TagWidth-1:0] iid_t;
    typedef logic [           WarpWidth-1:0] act_mask_t;
    typedef logic [RegWidth * WarpWidth-1:0] warp_data_t;
    typedef logic [    WidWidth-1:0] wid_t;
    typedef logic [EncInstWidth-1:0] enc_inst_t;

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
        bgpu_inst_t inst;
        reg_idx_t dst;
        logic     [OperandsPerInst-1:0] operands_required;
        reg_idx_t [OperandsPerInst-1:0] operands;
    } dec_to_ib_data_t;

    // Multi Warp Dispatcher to Register Operand Collector Stage type
    typedef struct packed {
        iid_t tag;
        pc_t pc;
        act_mask_t act_mask;
        bgpu_inst_t inst;
        reg_idx_t dst;
        logic     [OperandsPerInst-1:0] operands_required;
        reg_idx_t [OperandsPerInst-1:0] operands;
    } disp_to_opc_data_t;

    // Register Operand Collector Stage to Execution Units type
    typedef struct packed {
        iid_t tag;
        pc_t pc;
        act_mask_t act_mask;
        bgpu_inst_t inst;
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
    logic opc_to_eu_valid,  eu_to_opc_ready;
    logic opc_to_iu_valid,  iu_to_opc_ready;
    logic opc_to_lsu_valid, lsu_to_opc_ready;
    opc_to_eu_data_t opc_to_eu_data;

    // Execution Units to Register Operand Collector Stage
    logic eu_to_opc_valid, opc_to_eu_ready;
    logic iu_to_rc_valid,  rc_to_iu_ready;
    logic lsu_to_rc_valid, rc_to_lsu_ready;
    eu_to_opc_data_t eu_to_opc_data, iu_to_rc_data, lsu_to_rc_data;

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
        .PcWidth        ( PcWidth         ),
        .NumWarps       ( NumWarps        ),
        .WarpWidth      ( WarpWidth       ),
        .EncInstWidth   ( EncInstWidth    ),
        .RegIdxWidth    ( RegIdxWidth     ),
        .OperandsPerInst( OperandsPerInst )
    ) i_decoder (
        .dec_ready_o  ( dec_to_ic_ready_d         ),
        .ic_valid_i   ( ic_to_dec_valid_q         ),
        .ic_pc_i      ( ic_to_dec_data_q.pc       ),
        .ic_act_mask_i( ic_to_dec_data_q.act_mask ),
        .ic_warp_id_i ( ic_to_dec_data_q.warp_id  ),
        .ic_inst_i    ( ic_to_dec_data_q.inst     ),

        .disp_ready_i           ( ib_to_dec_ready_q                  ),
        .dec_valid_o            ( dec_to_ib_valid_d                  ),
        .dec_pc_o               ( dec_to_ib_data_d.pc                ),
        .dec_act_mask_o         ( dec_to_ib_data_d.act_mask          ),
        .dec_warp_id_o          ( dec_to_ib_data_d.warp_id           ),
        .dec_inst_o             ( dec_to_ib_data_d.inst              ),
        .dec_dst_o              ( dec_to_ib_data_d.dst               ),
        .dec_operands_required_o( dec_to_ib_data_d.operands_required ),
        .dec_operands_o         ( dec_to_ib_data_d.operands          ),

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
        .OperandsPerInst      ( OperandsPerInst       )
    ) i_warp_dispatcher (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .fe_handshake_i( fe_to_ic_valid_d && ic_to_fe_ready_q ),
        .fe_warp_id_i  ( fe_to_ic_data_d.warp_id              ),

        .ib_space_available_o( ib_space_available ),

        .ib_ready_o             ( ib_to_dec_ready_d                  ),
        .dec_valid_i            ( dec_to_ib_valid_q                  ),
        .dec_pc_i               ( dec_to_ib_data_q.pc                ),
        .dec_act_mask_i         ( dec_to_ib_data_q.act_mask          ),
        .dec_warp_id_i          ( dec_to_ib_data_q.warp_id           ),
        .dec_inst_i             ( dec_to_ib_data_q.inst              ),
        .dec_dst_i              ( dec_to_ib_data_q.dst               ),
        .dec_operands_required_i( dec_to_ib_data_q.operands_required ),
        .dec_operands_i         ( dec_to_ib_data_q.operands          ),

        .opc_ready_i             ( opc_to_disp_ready                  ),
        .disp_valid_o            ( disp_to_opc_valid                  ),
        .disp_tag_o              ( disp_to_opc_data.tag               ),
        .disp_pc_o               ( disp_to_opc_data.pc                ),
        .disp_act_mask_o         ( disp_to_opc_data.act_mask          ),
        .disp_inst_o             ( disp_to_opc_data.inst              ),
        .disp_dst_o              ( disp_to_opc_data.dst               ),
        .disp_operands_required_o( disp_to_opc_data.operands_required ),
        .disp_operands_o         ( disp_to_opc_data.operands          ),

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

        .opc_ready_o        ( opc_to_disp_ready                  ),
        .disp_valid_i       ( disp_to_opc_valid                  ),
        .disp_tag_i         ( disp_to_opc_data.tag               ),
        .disp_pc_i          ( disp_to_opc_data.pc                ),
        .disp_act_mask_i    ( disp_to_opc_data.act_mask          ),
        .disp_inst_i        ( disp_to_opc_data.inst              ),
        .disp_dst_i         ( disp_to_opc_data.dst               ),
        .disp_src_required_i( disp_to_opc_data.operands_required ),
        .disp_src_i         ( disp_to_opc_data.operands          ),

        .eu_ready_i        ( eu_to_opc_ready         ),
        .opc_valid_o       ( opc_to_eu_valid         ),
        .opc_tag_o         ( opc_to_eu_data.tag      ),
        .opc_pc_o          ( opc_to_eu_data.pc       ),
        .opc_act_mask_o    ( opc_to_eu_data.act_mask ),
        .opc_inst_o        ( opc_to_eu_data.inst     ),
        .opc_dst_o         ( opc_to_eu_data.dst      ),
        .opc_operand_data_o( opc_to_eu_data.operands ),

        .opc_to_eu_ready_o( opc_to_eu_ready     ),
        .eu_valid_i       ( eu_to_opc_valid     ),
        .eu_tag_i         ( eu_to_opc_data.tag  ),
        .eu_dst_i         ( eu_to_opc_data.dst  ),
        .eu_data_i        ( eu_to_opc_data.data )
    );

    // #######################################################################################
    // # Execution Unit Demux                                                                #
    // #######################################################################################

    stream_demux #(
        .N_OUP(2)
    ) i_eu_demux (
        .inp_valid_i( opc_to_eu_valid ),
        .inp_ready_o( eu_to_opc_ready ),

        .oup_sel_i( opc_to_eu_data.inst.eu[0] ),

        .oup_valid_o({ opc_to_lsu_valid, opc_to_iu_valid }),
        .oup_ready_i({ lsu_to_opc_ready, iu_to_opc_ready })
    );

    `ifndef SYNTHESIS
        assert property (@(posedge clk_i) opc_to_eu_valid
            |-> opc_to_eu_data.inst.eu inside {BGPU_EU_IU, BGPU_EU_LSU})
            else $error("Invalid execution unit type: %0d", opc_to_eu_data.inst.eu);
    `endif

    // #######################################################################################
    // # Execution Units                                                                     #
    // #######################################################################################

    // Integer Unit
    integer_unit #(
        .NumTags        ( NumTags         ),
        .NumWarps       ( NumWarps        ),
        .RegWidth       ( RegWidth        ),
        .WarpWidth      ( WarpWidth       ),
        .OperandsPerInst( OperandsPerInst ),
        .RegIdxWidth    ( RegIdxWidth     )
    ) i_integer_unit (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .eu_to_opc_ready_o   ( iu_to_opc_ready                ),
        .opc_to_eu_valid_i   ( opc_to_iu_valid                ),
        .opc_to_eu_tag_i     ( opc_to_eu_data.tag             ),
        .opc_to_eu_inst_sub_i( opc_to_eu_data.inst.subtype.iu ),
        .opc_to_eu_dst_i     ( opc_to_eu_data.dst             ),
        .opc_to_eu_operands_i( opc_to_eu_data.operands        ),

        .rc_to_eu_ready_i( rc_to_iu_ready     ),
        .eu_to_rc_valid_o( iu_to_rc_valid     ),
        .eu_to_rc_tag_o  ( iu_to_rc_data.tag  ),
        .eu_to_rc_dst_o  ( iu_to_rc_data.dst  ),
        .eu_to_rc_data_o ( iu_to_rc_data.data )
    );

    // Load Store Unit
    load_store_unit #(
        .RegWidth              ( RegWidth               ),
        .WarpWidth             ( WarpWidth              ),
        .OperandsPerInst       ( OperandsPerInst        ),
        .RegIdxWidth           ( RegIdxWidth            ),
        .iid_t                 ( iid_t                  ),
        .AddressWidth          ( AddressWidth           ),
        .BlockIdxBits          ( BlockIdxBits           ),
        .OutstandingReqIdxWidth( OutstandingReqIdxWidth )
    ) i_load_store_unit (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .eu_to_opc_ready_o   ( lsu_to_opc_ready                ),
        .opc_to_eu_valid_i   ( opc_to_lsu_valid                ),
        .opc_to_eu_tag_i     ( opc_to_eu_data.tag              ),
        .opc_to_eu_inst_sub_i( opc_to_eu_data.inst.subtype.lsu ),
        .opc_to_eu_act_mask_i( opc_to_eu_data.act_mask         ),
        .opc_to_eu_dst_i     ( opc_to_eu_data.dst              ),
        .opc_to_eu_operands_i( opc_to_eu_data.operands         ),

        .rc_to_eu_ready_i( rc_to_lsu_ready     ),
        .eu_to_rc_valid_o( lsu_to_rc_valid     ),
        .eu_to_rc_tag_o  ( lsu_to_rc_data.tag  ),
        .eu_to_rc_dst_o  ( lsu_to_rc_data.dst  ),
        .eu_to_rc_data_o ( lsu_to_rc_data.data ),

        .mem_ready_i      ( mem_ready_i       ),
        .mem_req_valid_o  ( mem_req_valid_o   ),
        .mem_req_id_o     ( mem_req_id_o      ),
        .mem_req_addr_o   ( mem_req_addr_o    ),
        .mem_req_we_mask_o( mem_req_we_mask_o ),
        .mem_req_wdata_o  ( mem_req_wdata_o   ),

        .mem_rsp_valid_i  ( mem_rsp_valid_i   ),
        .mem_rsp_id_i     ( mem_rsp_id_i      ),
        .mem_rsp_data_i   ( mem_rsp_data_i    )
    );

    // #######################################################################################
    // # Execution Unit Result Collector                                                     #
    // #######################################################################################

    stream_arbiter #(
        .DATA_T ( eu_to_opc_data_t ),
        .N_INP  ( 2                ),
        .ARBITER( "rr"             )
    ) i_result_collector (
        .clk_i        ( clk_i           ),
        .rst_ni       ( rst_ni          ),
        .inp_data_i   ({ iu_to_rc_data,  lsu_to_rc_data  }),
        .inp_valid_i  ({ iu_to_rc_valid, lsu_to_rc_valid }),
        .inp_ready_o  ({ rc_to_iu_ready, rc_to_lsu_ready }),

        .oup_data_o   ( eu_to_opc_data   ),
        .oup_valid_o  ( eu_to_opc_valid  ),
        .oup_ready_i  ( opc_to_eu_ready  )
    );

endmodule : compute_unit
