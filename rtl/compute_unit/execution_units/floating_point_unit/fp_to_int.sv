// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Converts a floating point number to a signed integer
module fp_to_int #(
    /// Width of the Operands
    parameter int DataWidth = 32,

    /// Latency of the unit
    parameter int unsigned Latency = 1,

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

    IEEE2INT #(
        .DataWidth( DataWidth ),
        .Latency  ( Latency   )
    ) i_ieee2int (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .ieee_i( fp_i  ),
        .int_o ( int_o ),

        .overflow_o( /* Unused */ )
    );

endmodule : fp_to_int
