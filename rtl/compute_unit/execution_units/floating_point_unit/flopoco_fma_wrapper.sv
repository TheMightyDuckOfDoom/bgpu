// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "common_cells/registers.svh"

/// Wrapper for the Flopoco FMA unit
// Computes (A * B) + C
// Actual latency is +1 than Flopoco FMA
module flopoco_fma_wrapper #(
    /// Width of the Operands
    parameter int DataWidth = 32,

    /// Tag to be passed down the pipeline
    parameter type tag_t = logic,

    /// Dependent parameter, do **not** overwrite.
    parameter type data_t = logic [DataWidth-1:0]
) (
    // Clock and Reset
    input logic clk_i,
    input logic rst_ni,

    // Operands
    input logic  valid_i,
    input tag_t  tag_i,
    input logic  negate_a_i,
    input logic  negate_c_i,
    input data_t operand_a_i,
    input data_t operand_b_i,
    input data_t operand_c_i,

    // Result
    output logic  valid_o,
    output tag_t  tag_o,
    output data_t result_o
);
    // #######################################################################################
    // # Local Parameters                                                                    #
    // #######################################################################################

    // Determine latency based on DataWidth
    localparam int unsigned Latency = (DataWidth == 32) ? `FMA_S_LATENCY : 0;

    // #######################################################################################
    // # Valid and Tag shift register                                                        #
    // #######################################################################################

    shift_reg_gated #(
        .Depth( Latency + 1 ),
        .dtype( tag_t   )
    ) i_valid_tag_sr (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .valid_i( valid_i ),
        .data_i ( tag_i   ),

        .valid_o( valid_o ),
        .data_o ( tag_o   )
    );

    // #######################################################################################
    // # Input Register                                                                      #
    // #######################################################################################

    logic  negate_a_q,  negate_c_q;
    data_t operand_a_q, operand_b_q, operand_c_q;

    `FF(negate_a_q,  negate_a_i,  '0, clk_i, rst_ni)
    `FF(negate_c_q,  negate_c_i,  '0, clk_i, rst_ni)
    `FF(operand_a_q, operand_a_i, '0, clk_i, rst_ni)
    `FF(operand_b_q, operand_b_i, '0, clk_i, rst_ni)
    `FF(operand_c_q, operand_c_i, '0, clk_i, rst_ni)

    // #######################################################################################
    // # Flopoco FMA (A*B)+C                                                                 #
    // #######################################################################################

    // Single precision FMA
    if (DataWidth == 32) begin : gen_fma_s
        if (Latency == 1) begin
            IEEEFMA_S1 i_fma_s (
                .clk( clk_i   ),
                .rst( !rst_ni ),

                .A( operand_a_q ),
                .B( operand_b_q ),
                .C( operand_c_q ),

                .negateAB( negate_a_q ),
                .negateC ( negate_c_q ),

                .RndMode( 'd0 ), // Non Functional

                .R( result_o )
            );
        end else if (Latency == 2) begin
            IEEEFMA_S2 i_fma_s (
                .clk( clk_i   ),
                .rst( !rst_ni ),

                .A( operand_a_q ),
                .B( operand_b_q ),
                .C( operand_c_q ),

                .negateAB( negate_a_q ),
                .negateC ( negate_c_q ),

                .RndMode( 'd0 ), // Non Functional

                .R( result_o )
            );
        end else if (Latency == 3) begin
            IEEEFMA_S3 i_fma_s (
                .clk( clk_i   ),
                .rst( !rst_ni ),

                .A( operand_a_q ),
                .B( operand_b_q ),
                .C( operand_c_q ),

                .negateAB( negate_a_q ),
                .negateC ( negate_c_q ),

                .RndMode( 'd0 ), // Non Functional

                .R( result_o )
            );
        end else if (Latency == 4) begin
            IEEEFMA_S4 i_fma_s (
                .clk( clk_i   ),
                .rst( !rst_ni ),

                .A( operand_a_q ),
                .B( operand_b_q ),
                .C( operand_c_q ),

                .negateAB( negate_a_q ),
                .negateC ( negate_c_q ),

                .RndMode( 'd0 ), // Non Functional

                .R( result_o )
            );
        end else if (Latency == 6) begin
            IEEEFMA_S6 i_fma_s (
                .clk( clk_i   ),
                .rst( !rst_ni ),

                .A( operand_a_q ),
                .B( operand_b_q ),
                .C( operand_c_q ),

                .negateAB( negate_a_q ),
                .negateC ( negate_c_q ),

                .RndMode( 'd0 ), // Non Functional

                .R( result_o )
            );
        end else begin
            initial $error("FMA: Unsupported Latency %0d for DataWidth %0d", Latency, DataWidth);
        end
    end : gen_fma_s

    // #######################################################################################
    // # Assertions                                                                  #
    // #######################################################################################

    // Check that DataWidth is supported
    initial assert (DataWidth == 32)
        else $error("FMA Wrapper: Unsupported DataWidth %0d", DataWidth);

endmodule : flopoco_fma_wrapper
