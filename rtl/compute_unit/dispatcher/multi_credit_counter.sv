// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Author: Fabian Schuiki <fschuiki@iis.ee.ethz.ch>
// Author: Paul Scheffler <paulsc@iis.ee.ethz.ch>

`include "common_cells/registers.svh"
`include "common_cells/assertions.svh"

module multi_credit_counter #(
    /// Number of credits to take at once
    parameter int unsigned NumTake         = 1,
    // Number of credits to give at once
    parameter int unsigned NumGive         = 1,
    /// Number of credits to manage
    parameter int unsigned NumCredits      = 1,
    /// Whether credit is full or empty on reset
    parameter bit          InitCreditEmpty = 1'b0,
    /// Derived parameters *Do not override*
    parameter int unsigned CreditWidth     = $clog2(NumCredits),
    parameter type         credit_cnt_t    = logic [CreditWidth:0],
    parameter credit_cnt_t InitNumCredits  = InitCreditEmpty ? '0 : NumCredits[CreditWidth:0]
) (
    input  logic clk_i,
    input  logic rst_ni,

    output credit_cnt_t credit_o,

    input  logic [NumGive-1:0] credit_give_i,
    input  logic [NumTake-1:0] credit_take_i,
    input  logic               credit_init_i,  // Reinitialize (soft-reset) credit; takes priority

    output logic credit_left_o,
    output logic credit_crit_o,  // Giving one more credit will fill the credits
    output logic credit_full_o
);

    credit_cnt_t credit_d, credit_q;
    credit_cnt_t increment, decrement;

    always_comb begin : decrement_logic
        decrement = '0;
        for (int i = 0; i < NumTake; i++) begin
            if (credit_take_i[i])
                decrement = decrement + 'd1;
        end
    end : decrement_logic

    always_comb begin : increment_logic
        increment = '0;
        for (int i = 0; i < NumGive; i++) begin
            if (credit_give_i[i])
                increment = increment + 'd1;
        end
    end : increment_logic

    assign credit_d  = credit_q + increment - decrement;

    `FFARNC(credit_q, credit_d, credit_init_i, InitNumCredits, clk_i, rst_ni)

    assign credit_o        = credit_q;
    assign credit_left_o   = (credit_q != '0);
    assign credit_crit_o   = (credit_q == (NumCredits[CreditWidth:0] - 'd1));
    assign credit_full_o   = (credit_q == NumCredits[CreditWidth:0]);

    `ASSERT_NEVER(CreditUnderflow, (decrement > increment) && ((decrement + credit_o) < increment))
    `ASSERT_NEVER(CreditOverflow, (increment > decrement) && ((decrement + credit_o) > (NumCredits[CreditWidth:0] + increment)))

    `ASSERT_INIT(NumCreditsValid, NumCredits > 0)
    `ASSERT_INIT(NumTakeValid, (NumTake <= NumCredits) && (NumTake > 0))

endmodule : multi_credit_counter
