// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Converts a signed integer to floating point
module flopoco_int_to_fp #(
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
    input data_t int_i,

    // Result
    output logic  valid_o,
    output tag_t  tag_o,
    output data_t fp_o
);
    // #######################################################################################
    // # Local Parameters                                                                    #
    // #######################################################################################

    // Determine latency based on DataWidth
    localparam int unsigned Latency = (DataWidth == 32) ? `INT2FP_S_LATENCY : 0;

    // #######################################################################################
    // # Valid and Tag shift register                                                        #
    // #######################################################################################

    shift_reg_gated #(
        .Depth( Latency ),
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
    // # Flopoco Conversion                                                                  #
    // #######################################################################################

    logic [DataWidth+1:0] flopoco_fp;

    // Single precision Int2FP
    if (DataWidth == 32) begin : gen_int2fp_s
        if (Latency == 0) begin
            Fix2FP_S0 i_int2fp_s (
                .clk( clk_i   ),
                .rst( !rst_ni ),

                .I ( int_i ),

                .O ( flopoco_fp )
            );
        end else if (Latency == 1) begin
            Fix2FP_S1 i_int2fp_s (
                .clk( clk_i   ),
                .rst( !rst_ni ),

                .I ( int_i ),

                .O ( flopoco_fp )
            );
        end else if (Latency == 2) begin
            Fix2FP_S2 i_int2fp_s (
                .clk( clk_i   ),
                .rst( !rst_ni ),

                .I ( int_i ),

                .O ( flopoco_fp )
            );
        end else begin
            initial $error("INT2FP: Unsupported Latency %0d for DataWidth %0d", Latency, DataWidth);
        end

        FP2IEEE_S0 i_fp2ieee_s (
            .clk( clk_i   ),
            .rst( !rst_ni ),

            .X( flopoco_fp ),

            .R( fp_o )
        );
    end : gen_int2fp_s

    // #######################################################################################
    // # Assertions                                                                  #
    // #######################################################################################

    // Check that DataWidth is supported
    initial assert (DataWidth == 32)
        else $error("INT2FP: Unsupported DataWidth %0d", DataWidth);

endmodule : flopoco_int_to_fp
