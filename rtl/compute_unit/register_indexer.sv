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
    parameter int unsigned WidWidth         = NumWarps > 1 ? $clog2(NumWarps) : 1,
    parameter int unsigned BankSelWidth     = NumBanks > 1 ? $clog2(NumBanks) : 1,
    parameter int unsigned BankRegAddrWidth = RegistersPerBank > 1 ? $clog2(RegistersPerBank) : 1,
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
    if (NumBanks > 1) begin : gen_multi_bank
        // Multiple Warps to Multiple Banks
        if (NumWarps > 1) begin : gen_multi_warp
            assign bank_sel_o = hash[WidWidth+RegIdxWidth-1-:BankSelWidth];
        end : gen_multi_warp

        // Single Warp to Multiple Banks -> Distribute the registers among the banks
        else if (NumWarps == 1) begin : gen_single_warp
            // If there is only one warp, the bank selection is based on the register index
            assign bank_sel_o = hash[RegIdxWidth-1-:BankSelWidth];
        end : gen_single_warp
    end : gen_multi_bank
    else begin : gen_single_bank
        // Single Bank Case

        // If there is only one bank, set bank_sel_o to zero
        assign bank_sel_o = '0;
    end : gen_single_bank

    // Select lower bits for register address within the bank
    assign bank_reg_addr_o = hash[BankRegAddrWidth-1:0];

    // ################################################################################
    // # Assertions                                                                   #
    // ################################################################################

    // Check that the widths make sense
    `ifndef SYNTHESIS
        initial begin : asserts
            if (NumBanks == 1 && NumWarps > 1) begin
                assert (WidWidth + RegIdxWidth == BankRegAddrWidth)
                else $error("WidWidth+RegIdxWidth != BankRegAddrWidth");
            end else if (NumBanks > 1 && NumWarps == 1) begin
                assert (RegIdxWidth == BankSelWidth + BankRegAddrWidth)
                else $error("RegIdxWidth != BankSelWidth + BankRegAddrWidth");
            end else begin
                assert (WidWidth + RegIdxWidth == BankSelWidth + BankRegAddrWidth)
                else $error("WidWidth+RegIdxWidth != BankSelWidth + BankRegAddrWidth");
            end
        end : asserts
    `endif

endmodule : register_indexer
