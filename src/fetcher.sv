// Copyright Feb 2025 Tobias Senti
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
    /// Number of warps
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

    /// From instruction buffer -> which warp has space for a new instruction?
    input  logic [NumWarps-1:0] ib_space_available_i,

    /// To/From instruction cache
    input  logic      ic_ready_i,
    output logic      ic_pc_valid_o,
    output pc_t       ic_pc_o,
    output act_mask_t ic_act_mask_o,
    output wid_t      ic_warp_id_o
);
    // Arbiter data input
    typedef struct packed {
        pc_t pc;
        act_mask_t act_mask;
    } arb_warp_data_t;

    arb_warp_data_t [NumWarps-1:0] arb_in_data;
    logic [NumWarps-1:0] rr_warp_ready;

    // Arbiter data output
    arb_warp_data_t arb_sel_data;
    logic [NumWarps-1:0] arb_gnt;

    // Data from reconvergence stack
    logic      [NumWarps-1:0] rs_warp_ready;
    pc_t       [NumWarps-1:0] rs_warp_pc;
    act_mask_t [NumWarps-1:0] rs_warp_act_mask;

    // Generate arbiter data
    for(genvar i = 0; i < NumWarps; i++) begin : gen_arb_data
        assign arb_in_data[i].pc       = rs_warp_pc[i];
        assign arb_in_data[i].act_mask = rs_warp_act_mask[i];
    end

    // Round robin arbiter
    rr_arb_tree #(
        .DataType ( arb_warp_data_t ),
        .NumIn    ( NumWarps ),
        .ExtPrio  ( 1'b0     ),
        .AxiVldRdy( 1'b0     ),
        .LockIn   ( 1'b1     ),
        .FairArb  ( 1'b1     )
    ) i_rr_arb (
        .clk_i ( clk_i),
        .rst_ni( rst_ni),
        
        .req_i  ( ib_space_available_i ),
        .gnt_o  ( arb_gnt              ),
        .data_i ( arb_in_data          ),

        // Directly to instruction cache
        .req_o ( ic_pc_valid_o ),
        .gnt_i ( ic_ready_i    ),
        .data_o( arb_sel_data  ),
        .idx_o ( ic_warp_id_o  ),
        
        // Unused
        .flush_i( 1'b0 ),
        .rr_i   ( '0   )
    );
    
    // Warp can be fetched if there is space in the instruction buffer and reconvergence stack is ready
    assign rr_warp_ready = ib_space_available_i & rs_warp_ready;

    // Reconvergence stack
    dummy_reconvergence_stack #(
        .PcWidth   ( PcWidth   ),
        .NumWarps  ( NumWarps  ),
        .WarpWidth ( WarpWidth )
    ) i_reconvergence_stack (
        .clk_i             ( clk_i  ),
        .rst_ni            ( rst_ni ),

        .instruction_decoded_i( 1'b0 ),
        .decode_wid_i         ( '0   ),

        .warp_selected_i    ( arb_gnt             ),
        .warp_ready_o       ( rs_warp_ready       ),
        .warp_pc_o          ( rs_warp_pc          ),
        .warp_act_mask_o    ( rs_warp_act_mask    )
    );

    // Outputs to instruction cache
    assign ic_pc_o       = arb_sel_data.pc;
    assign ic_act_mask_o = arb_sel_data.act_mask;

endmodule
