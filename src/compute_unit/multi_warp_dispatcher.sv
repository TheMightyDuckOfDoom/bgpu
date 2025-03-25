// Copyright March 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Multi Warp Dispatcher
/// Contains a dispatcher per warp
module multi_warp_dispatcher #(
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
    parameter int  WidWidth   = $clog2(NumWarps),
    parameter type wid_t      = logic [ WidWidth-1:0],
    parameter type pc_t       = logic [  PcWidth-1:0],
    parameter type act_mask_t = logic [WarpWidth-1:0]
) (
    /// Clock and Reset
    input  logic clk_i,
    input  logic rst_ni,

    /// From fetcher -> which warp gets fetched next
    input  logic fe_handshake_i,
    input  wid_t fe_warp_id_i,

    /// From decoder
    output logic      ib_ready_o,
    input  logic      dec_valid_i,
    input  pc_t       dec_pc_i,
    input  act_mask_t dec_act_mask_i,
    input  wid_t      dec_warp_id_i,
    input  dec_inst_t dec_inst_i,

    /// To fetcher -> which warps have space for a new instruction?
    output logic [NumWarps-1:0] ib_space_available_o
);

    // #######################################################################################
    // # Dispatcher per warp                                                                 #
    // #######################################################################################

    logic [NumWarps-1:0] dec_valid_warp, ib_ready_warp, fe_handshake_warp;
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

    for(genvar warp = 0; warp < NumWarps; warp++) begin : gen_dispatcher
        dispatcher #(
            .PcWidth              ( PcWidth               ),
            .WarpWidth            ( WarpWidth             ),
            .WaitBufferSizePerWarp( WaitBufferSizePerWarp ),
            .RegIdxWidth          ( RegIdxWidth           ),
            .OperandsPerInst      ( OperandsPerInst       ),
            .dec_inst_t           ( dec_inst_t            )
        ) i_dispatcher (
            .clk_i ( clk_i  ),
            .rst_ni( rst_ni ),

            .fe_handshake_i ( fe_handshake_warp[warp] ),

            .disp_ready_o  ( ib_ready_warp[warp]  ),
            .dec_valid_i   ( dec_valid_warp[warp] ),
            .dec_pc_i      ( dec_pc_i             ),
            .dec_act_mask_i( dec_act_mask_i       ),
            .dec_inst_i    ( dec_inst_i           ),
        
            .ib_space_available_o( ib_space_available_o[warp] )
        );
    end : gen_dispatcher

endmodule : multi_warp_dispatcher
