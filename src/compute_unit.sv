// Copyright Feb 2025 Tobias Senti
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
    parameter int EncInstWidth = 32
) (
    // Clock and reset
    input logic clk_i,
    input logic rst_ni,

    // Dummy inputs / outputs
    input  logic [NumWarps-1:0] ib_space_available_i,
    input  logic dec_ready_i,
    output logic [PcWidth-1:0] dec_pc_o,
    output logic [WarpWidth-1:0] dec_act_mask_o,
    output logic [$clog2(NumWarps)-1:0] dec_warp_id_o,
    output logic [EncInstWidth-1:0] dec_inst_o,

    input logic dec_decoded_i,
    input logic [$clog2(NumWarps)-1:0] dec_decoded_warp_id_i
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
    logic dec_decoded;
    wid_t dec_decoded_warp_id;

    // #######################################################################################
    // # Fetcher                                                                             #
    // #######################################################################################

    fetcher #(
        .PcWidth  ( PcWidth   ),
        .NumWarps ( NumWarps  ),
        .WarpWidth( WarpWidth )
    ) fetcher_i (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .ib_space_available_i( ib_space_available ),

        .ic_ready_i   ( ic_to_fe_ready_q         ),
        .fe_valid_o   ( fe_to_ic_valid_d         ),
        .fe_pc_o      ( fe_to_ic_data_d.pc       ),
        .fe_act_mask_o( fe_to_ic_data_d.act_mask ),
        .fe_warp_id_o ( fe_to_ic_data_d.warp_id  ),

        .dec_decoded_i         ( dec_decoded         ),
        .dec_decoded_warp_id_i ( dec_decoded_warp_id )
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
        .MemoryFile  ( ""        ),
        .MemorySize  ( 0         ),
        .PcWidth     ( PcWidth   ),
        .NumWarps    ( NumWarps  ),
        .WarpWidth   ( WarpWidth ),
        .EncInstWidth( 32        )
    ) i_instruction_cache (
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
    // # Dummy Inputs / Outputs                                                              #
    // #######################################################################################

    assign ib_space_available = ib_space_available_i;

    assign dec_to_ic_ready_d = dec_ready_i;
    assign dec_pc_o          = ic_to_dec_data_q.pc;
    assign dec_act_mask_o    = ic_to_dec_data_q.act_mask;
    assign dec_warp_id_o     = ic_to_dec_data_q.warp_id;
    assign dec_inst_o        = ic_to_dec_data_q.inst;

    assign dec_decoded         = dec_decoded_i;
    assign dec_decoded_warp_id = dec_decoded_warp_id_i;

endmodule : compute_unit
