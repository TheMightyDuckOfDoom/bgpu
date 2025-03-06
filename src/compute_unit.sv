// Copyright Feb-March 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Compute Unit
module compute_unit #(
    /// Width of the Program Counter
    parameter int PcWidth = 16,
    /// Number of warps
    parameter int NumWarps = 8,
    /// Number of threads per warp
    parameter int WarpWidth = 4,
    /// Encoded instruction width
    parameter int EncInstWidth = 32,

    parameter type dec_inst_t = struct packed {
        logic [EncInstWidth-1:0] dummy;
    }
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

    input  logic [NumWarps-1:0] ib_space_available_i,

    input  logic disp_ready_i,
    output logic dec_valid_o,
    output logic [PcWidth-1:0] dec_pc_o,
    output logic [WarpWidth-1:0] dec_act_mask_o,
    output logic [$clog2(NumWarps)-1:0] dec_warp_id_o,
    output dec_inst_t dec_inst_o
);
    // #######################################################################################
    // # Localparams                                                                         #
    // #######################################################################################

    localparam int WidWidth = $clog2(NumWarps);

    // #######################################################################################
    // # Typedefs                                                                            #
    // #######################################################################################

    // Typedefs
    typedef logic [    WidWidth-1:0] wid_t;
    typedef logic [     PcWidth-1:0] pc_t;
    typedef logic [   WarpWidth-1:0] act_mask_t;
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

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Instruction buffer
    logic [NumWarps-1:0] ib_space_available; // Which warp has space for a new instruction?

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

    // Decoder to Dispatcher
    logic      dec_to_disp_valid, disp_to_dec_ready;
    pc_t       dec_to_disp_pc;
    act_mask_t dec_to_disp_act_mask;
    wid_t      dec_to_disp_warp_id;
    dec_inst_t dec_to_disp_inst;

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
        .MemorySize  ( 1024      ),
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

        .disp_ready_i  ( disp_to_dec_ready    ),
        .dec_valid_o   ( dec_to_disp_valid    ),
        .dec_pc_o      ( dec_to_disp_pc       ),
        .dec_act_mask_o( dec_to_disp_act_mask ),
        .dec_warp_id_o ( dec_to_disp_warp_id  ),
        .dec_inst_o    ( dec_to_disp_inst     ),

        .dec_decoded_o         ( dec_to_fetch_decoded         ),
        .dec_stop_warp_o       ( dec_to_fetch_stop_warp       ),
        .dec_decoded_warp_id_o ( dec_to_fetch_decoded_warp_id ),
        .dec_decoded_next_pc_o ( dec_to_fetch_decoded_next_pc )
    );

    // #######################################################################################
    // # Dummy Inputs / Outputs                                                              #
    // #######################################################################################

    assign ib_space_available = ib_space_available_i;

    assign disp_to_dec_ready = disp_ready_i;
    assign dec_valid_o       = dec_to_disp_valid;
    assign dec_pc_o          = dec_to_disp_pc;
    assign dec_act_mask_o    = dec_to_disp_act_mask;
    assign dec_warp_id_o     = dec_to_disp_warp_id;
    assign dec_inst_o        = dec_to_disp_inst;

endmodule : compute_unit
