// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`ifndef BGPU_INSTRUCTIONS_SVH_
`define BGPU_INSTRUCTIONS_SVH_

typedef enum logic [1:0] {
    BGPU_INST_TYPE_IU = 'd0
} bgpu_eu_e;

typedef enum logic [5:0] {
    IU_ADD = 'h00, // Add operands
    IU_TID = 'h01, // Get thread ID inside a warp
    IU_LDI = 'h02  // Load immediate -> concatenate operands register index
} bgpu_inst_subtype_e;

typedef struct packed {
    bgpu_eu_e           eu;
    bgpu_inst_subtype_e subtype;
} bgpu_inst_t;

`ifndef SYNTHESIS
    `define BGPU_INT_UNIT_VALID_SUBTYPES {\
        IU_ADD,\
        IU_TID,\
        IU_LDI\
    }
`endif

`endif
