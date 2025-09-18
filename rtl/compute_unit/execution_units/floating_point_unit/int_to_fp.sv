// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Converts a signed integer to floating point
module int_to_fp #(
    /// Width of the Operands
    parameter int DataWidth = 32,

    /// Latency of the unit
    parameter int unsigned Latency = 2,

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
    // # Conversion                                                                          #
    // #######################################################################################

    INT2IEEE #(
        .DataWidth( DataWidth ),
        .Latency  ( Latency   )
    ) i_int2fp (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .int_i ( int_i  ),
        .ieee_o( fp_o   )
    );

endmodule : int_to_fp
