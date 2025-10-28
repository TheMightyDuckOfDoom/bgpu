// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Floating Point Operation
// - Division
// - Exponentiation
// - Logarithm
// - Square Root
module fop #(
    /// Width of the Operands
    parameter int DataWidth = 32,
    /// Operation to be implemented by this unit
    parameter string Operation = "DIV",
    /// Latency of the unit
    parameter int unsigned Latency = 8,
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
    input data_t operand_a_i,
    input data_t operand_b_i,

    // Result
    output logic  valid_o,
    output tag_t  tag_o,
    output data_t result_o
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
    // # Datapath                                                                            #
    // #######################################################################################

    if (Operation == "DIV") begin : gen_divider
        // Divider
        IEEEDiv #(
            .DataWidth( DataWidth ),
            .Latency  ( Latency   )
        ) i_ieee_div (
            .clk_i ( clk_i  ),
            .rst_ni( rst_ni ),

            .operand_a_i( operand_a_i ),
            .operand_b_i( operand_b_i ),

            .result_o( result_o )
        );
    end else if (Operation == "EXP") begin : gen_exponent
        // Exponentiation
        IEEEExp #(
            .DataWidth( DataWidth ),
            .Latency  ( Latency   )
        ) i_ieee_exp (
            .clk_i ( clk_i  ),
            .rst_ni( rst_ni ),

            .operand_a_i( operand_a_i ),

            .result_o( result_o )
        );
    end else if (Operation == "LOG") begin : gen_logarithm
        // Logarithm
        IEEELog #(
            .DataWidth( DataWidth ),
            .Latency  ( Latency   )
        ) i_ieee_log (
            .clk_i ( clk_i  ),
            .rst_ni( rst_ni ),

            .operand_x_i( operand_a_i ),

            .result_o( result_o )
        );
    end else if (Operation == "SQRT") begin : gen_sqrt
        // Square Root
        IEEESqrt #(
            .DataWidth( DataWidth ),
            .Latency  ( Latency   )
        ) i_ieee_sqrt (
            .clk_i ( clk_i  ),
            .rst_ni( rst_ni ),

            .operand_x_i( operand_a_i ),

            .result_o( result_o )
        );
    end else begin : gen_invalid_op
        // Invalid Operation
        initial $fatal(1, "fdiv: Invalid Operation '%s' specified!", Operation);
    end

endmodule : fop
