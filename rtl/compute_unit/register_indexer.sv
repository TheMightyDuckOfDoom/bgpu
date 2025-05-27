
// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Register Indexer
// Converts a WID+REG_IDX to Bank Select and Register Address within the bank.
module register_indexer #(
    /// Number of warps per compute unit
    parameter int unsigned NumWarps = 8,
    /// How many registers can each warp access as operand or destination
    parameter int unsigned RegIdxWidth = 6,
    /// How many banks are there in the register file
    parameter int unsigned NumBanks = 4,
    /// How many registers are there per bank
    parameter int unsigned RegistersPerBank = 32,

    /// Dependent parameter, do **not** overwrite.
    parameter int unsigned WidWidth         = $clog2(NumWarps),
    parameter int unsigned BankSelWidth     = $clog2(NumBanks),
    parameter int unsigned BankRegAddrWidth = $clog2(RegistersPerBank),
    parameter type         wid_t            = logic [WidWidth-1:0],
    parameter type         reg_idx_t        = logic [RegIdxWidth-1:0],
    parameter type         bank_sel_t       = logic [BankSelWidth-1:0],
    parameter type         bank_reg_addr_t  = logic [BankRegAddrWidth-1:0]
) (
    // Inputs
    input  wid_t     wid_i,
    input  reg_idx_t reg_idx_i,

    // Outputs
    output bank_sel_t      bank_sel_o,
    output bank_reg_addr_t bank_reg_addr_o
);
    // ################################################################################
    // # Typedefs                                                                     #
    // ################################################################################

    logic [WidWidth+RegIdxWidth-1:0] hash;

    // ################################################################################
    // # Calculate Bank Select and Register Address within the bank                   #
    // ################################################################################

    // Combine WID and REG_IDX into a single hash value
    assign hash = {wid_i, reg_idx_i};

    // Select upper bits for bank selection
    assign bank_sel_o = hash[WidWidth+RegIdxWidth-1:BankRegAddrWidth];

    // Select lower bits for register address within the bank
    assign bank_reg_addr_o = hash[BankRegAddrWidth-1:0];

    // ################################################################################
    // # Assertions                                                                   #
    // ################################################################################

    // Check that the widths make sense
    initial assert (WidWidth + RegIdxWidth == BankSelWidth + BankRegAddrWidth)
        else $error("Register indexer: Width mismatch between WID+REG_IDX and BankSel+BankRegAddr");

endmodule : register_indexer
