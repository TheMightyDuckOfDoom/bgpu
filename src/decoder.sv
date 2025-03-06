// Copyright Feb-March 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Decoder
module decoder #(
    /// Width of the Program Counter
    parameter int PcWidth = 32,
    /// Number of warps per compute unit
    parameter int NumWarps = 8,
    /// Number of threads per warp
    parameter int WarpWidth = 32,
    /// Encoded instruction width
    parameter int EncInstWidth = 32,

    parameter type dec_inst_t = logic,

    /// Dependent parameter, do **not** overwrite.
    parameter int  WidWidth   = $clog2(NumWarps),
    parameter type wid_t      = logic [    WidWidth-1:0],
    parameter type pc_t       = logic [     PcWidth-1:0],
    parameter type act_mask_t = logic [   WarpWidth-1:0],
    parameter type enc_inst_t = logic [EncInstWidth-1:0]
) (
    // From Instruction Cache
    output logic      dec_ready_o,
    input  logic      ic_valid_i,
    input  pc_t       ic_pc_i,
    input  act_mask_t ic_act_mask_i,
    input  wid_t      ic_warp_id_i,
    input  enc_inst_t ic_inst_i,

    // To Dispatcher
    input  logic      disp_ready_i,
    output logic      dec_valid_o,
    output pc_t       dec_pc_o,
    output act_mask_t dec_act_mask_o,
    output wid_t      dec_warp_id_o,
    output dec_inst_t dec_inst_o,

    // To Fetcher -> tells it what the next PC is
    output logic dec_decoded_o,
    output logic dec_stop_warp_o,
    output wid_t dec_decoded_warp_id_o,
    output pc_t  dec_decoded_next_pc_o
);
    // Pass through signals
    assign dec_ready_o    = disp_ready_i;
    assign dec_pc_o       = ic_pc_i;
    assign dec_act_mask_o = ic_act_mask_i;
    assign dec_warp_id_o  = ic_warp_id_i;

    // Instruction was decoded if a handshake between Decoder and Dispatcher happend
    assign dec_decoded_o         = dec_valid_o && disp_ready_i;
    assign dec_decoded_warp_id_o = dec_warp_id_o;
    assign dec_decoded_next_pc_o = dec_pc_o + 'd1;

    assign dec_stop_warp_o = &ic_inst_i;

    // Decode instruction
    always_comb begin : decode
        // Default
        dec_valid_o = ic_valid_i;
        dec_inst_o  = ic_inst_i;
    end
endmodule : decoder
