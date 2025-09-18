// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Converts a floating point number to a signed integer
module flopoco_fp_to_int #(
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
    input data_t fp_i,

    // Result
    output logic  valid_o,
    output tag_t  tag_o,
    output data_t int_o
);
    // #######################################################################################
    // # Local Parameters                                                                    #
    // #######################################################################################

    // Determine latency based on DataWidth
    localparam int unsigned Latency = (DataWidth == 32) ? `FP2INT_S_LATENCY : 0;

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

    // Single precision Fp2Int
    if (DataWidth == 32) begin : gen_fp2int_s
        IEEE2FP_S0 i_ieee2fp_s (
            .clk( clk_i   ),
            .rst( !rst_ni ),

            .X( fp_i ),

            .R( flopoco_fp )
        );

        if (Latency == 0) begin
            FP2Fix_S0 i_fp2int_s (
                .clk( clk_i   ),
                .rst( !rst_ni ),

                .X( flopoco_fp ),

                .R ( int_o        ),
                .ov( /* unused */ )
            );
        end else if (Latency == 1) begin
            FP2Fix_S1 i_fp2int_s (
                .clk( clk_i   ),
                .rst( !rst_ni ),

                .X( flopoco_fp ),

                .R ( int_o        ),
                .ov( /* unused */ )
            );
        end else begin
            initial $error("FP2INT: Unsupported Latency %0d for DataWidth %0d", Latency, DataWidth);
        end
    end : gen_fp2int_s

    // #######################################################################################
    // # Assertions                                                                  #
    // #######################################################################################

    // Check that DataWidth is supported
    initial assert (DataWidth == 32)
        else $error("FP2INT: Unsupported DataWidth %0d", DataWidth);

endmodule : flopoco_fp_to_int
