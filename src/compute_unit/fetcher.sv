// Copyright Feb-March 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Fetcher
/// contains the reconvergence stack
/// Outputs a PC to the instruction cache, if:
/// - There is space in the instruction buffer for a new instruction for a given warp
/// - The I-cache is ready to receive a new instruction to fetch
/// The PC of the warp comes from the reconvergence stack
/// If multiple warps are ready for fetching, a round-robin arbiter is used

module fetcher #(
    /// Width of the Program Counter
    parameter int PcWidth = 32,
    /// Number of warps per compute unit
    parameter int NumWarps = 8,
    /// Number of threads per warp
    parameter int WarpWidth = 32,

    /// Dependent parameter, do **not** overwrite.
    parameter int  WidWidth   = $clog2(NumWarps),
    parameter type wid_t      = logic [ WidWidth-1:0],
    parameter type pc_t       = logic [  PcWidth-1:0],
    parameter type act_mask_t = logic [WarpWidth-1:0]
) (
    /// Clock and reset
    input logic clk_i,
    input logic rst_ni,

    input  logic set_ready_i,
    output logic [NumWarps-1:0] warp_active_o,
    output logic [NumWarps-1:0] warp_stopped_o,

    /// From instruction buffer -> which warp has space for a new instruction?
    input  logic [NumWarps-1:0] ib_space_available_i,

    /// To/From instruction cache
    input  logic      ic_ready_i,
    output logic      fe_valid_o,
    output pc_t       fe_pc_o,
    output act_mask_t fe_act_mask_o,
    output wid_t      fe_warp_id_o,

    /// From Decoder
    input logic dec_decoded_i,
    input logic dec_stop_warp_i,
    input wid_t dec_decoded_warp_id_i,
    input pc_t  dec_decoded_next_pc_i
);
    // #######################################################################################
    // # Typedefs                                                                            #
    // #######################################################################################

    // Arbiter data input
    typedef struct packed {
        pc_t pc;
        act_mask_t act_mask;
    } arb_warp_data_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Arbiter data input
    arb_warp_data_t [NumWarps-1:0] arb_in_data;
    logic [NumWarps-1:0] rr_warp_ready;

    // Arbiter data output
    arb_warp_data_t arb_sel_data;
    logic [NumWarps-1:0] arb_gnt;

    // Data from reconvergence stack
    logic      [NumWarps-1:0] rs_warp_ready;
    pc_t       [NumWarps-1:0] rs_warp_pc;
    act_mask_t [NumWarps-1:0] rs_warp_act_mask;

    // #######################################################################################
    // # Round Robin Arbiter                                                                 #
    // #######################################################################################

    // Arbiter data input
    for(genvar i = 0; i < NumWarps; i++) begin : gen_arb_data
        assign arb_in_data[i].pc       = rs_warp_pc[i];
        assign arb_in_data[i].act_mask = rs_warp_act_mask[i];

        always_comb assert(!rs_warp_ready[i] || (rs_warp_ready[i] && rs_warp_act_mask[i] != '0))
        else $error("Warp is ready, but has no active threads");
    end : gen_arb_data

    // Warp can be fetched if there is space in the instruction buffer and reconvergence stack is ready
    assign rr_warp_ready = ib_space_available_i & rs_warp_ready;

    // Round robin arbiter
    rr_arb_tree #(
        .DataType ( arb_warp_data_t ),
        .NumIn    ( NumWarps ),
        .ExtPrio  ( 1'b0     ),
        .AxiVldRdy( 1'b0     ),
        .LockIn   ( 1'b1     ),
        .FairArb  ( 1'b1     )
    ) i_rr_arb (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .req_i  ( rr_warp_ready ),
        .gnt_o  ( arb_gnt       ),
        .data_i ( arb_in_data   ),

        // Directly to instruction cache
        .req_o ( fe_valid_o    ),
        .gnt_i ( ic_ready_i    ),
        .data_o( arb_sel_data  ),
        .idx_o ( fe_warp_id_o  ),

        // Unused
        .flush_i( 1'b0 ),
        .rr_i   ( '0   )
    );

    // #######################################################################################
    // # Reconvergence Stack                                                                 #
    // #######################################################################################

    dummy_reconvergence_stack #(
        .PcWidth   ( PcWidth   ),
        .NumWarps  ( NumWarps  ),
        .WarpWidth ( WarpWidth )
    ) i_reconvergence_stack (
        .clk_i             ( clk_i  ),
        .rst_ni            ( rst_ni ),

        .set_ready_i       ( set_ready_i ),

        .instruction_decoded_i( dec_decoded_i         ),
        .decode_stop_warp_i   ( dec_stop_warp_i       ),
        .decode_wid_i         ( dec_decoded_warp_id_i ),
        .decode_next_pc_i     ( dec_decoded_next_pc_i ),

        .warp_selected_i    ( arb_gnt             ),
        .warp_ready_o       ( rs_warp_ready       ),
        .warp_active_o      ( warp_active_o       ),
        .warp_stopped_o     ( warp_stopped_o      ),
        .warp_pc_o          ( rs_warp_pc          ),
        .warp_act_mask_o    ( rs_warp_act_mask    )
    );

    // #######################################################################################
    // # Outputs                                                                             #
    // #######################################################################################

    // To instruction cache
    assign fe_pc_o       = arb_sel_data.pc;
    assign fe_act_mask_o = arb_sel_data.act_mask;

endmodule : fetcher
