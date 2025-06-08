// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`ifndef BGPU_INSTRUCTIONS_SVH_
`define BGPU_INSTRUCTIONS_SVH_

typedef enum logic [1:0] {
    BGPU_INST_TYPE_IU  = 'd0,
    BGPU_INST_TYPE_LSU = 'd1
} bgpu_eu_e;

typedef enum logic [5:0] {
    IU_TID  = 'h00, // Get thread ID inside a warp

    IU_ADD  = 'h01, // Add operands
    IU_SUB  = 'h02, // Subtract operands
    IU_AND  = 'h03, // Bitwise AND operands
    IU_OR   = 'h04, // Bitwise OR operands
    IU_XOR  = 'h05, // Bitwise XOR operands

    IU_LDI  = 'h06, // Load immediate -> concatenate operands register index
    IU_ADDI = 'h07, // Add immediate -> add immediate value to first operand
    IU_SUBI = 'h08, // Subtract immediate -> subtract immediate value from first operand

    LSU_LOAD = 'h09, // Load from memory
    LSU_STORE_BYTE = 'h0A, // Store byte to memory
    LSU_STORE_HALF = 'h0B, // Store half-word to memory
    LSU_STORE_WORD = 'h0C  // Store word to memory
} bgpu_inst_subtype_e;

typedef struct packed {
    bgpu_eu_e           eu;
    bgpu_inst_subtype_e subtype;
} bgpu_inst_t;

// Both operands are registers
`define BGPU_INST_TWO_REG_OPERANDS {\
    IU_ADD,\
    IU_SUB,\
    IU_AND,\
    IU_OR,\
    IU_XOR,\
    LSU_LOAD,\
    LSU_STORE_BYTE,\
    LSU_STORE_HALF,\
    LSU_STORE_WORD\
}

// First operand is a register, second is an immediate value (register index)
`define BGPU_INST_REG_IMM_OPERANDS {\
    IU_ADDI,\
    IU_SUBI\
}

// Store operations
`define BGPU_INST_STORE {\
    LSU_STORE_BYTE,\
    LSU_STORE_HALF,\
    LSU_STORE_WORD\
}

`ifndef SYNTHESIS
    `define BGPU_INT_UNIT_VALID_SUBTYPES {\
        IU_TID,\
        IU_ADD,\
        IU_SUB,\
        IU_AND,\
        IU_OR,\
        IU_XOR,\
        IU_LDI,\
        IU_ADDI,\
        IU_SUBI\
    }

    `define BGPU_LOAD_STORE_UNIT_VALID_SUBTYPES {\
        LSU_LOAD,\
        LSU_STORE_BYTE,\
        LSU_STORE_HALF,\
        LSU_STORE_WORD\
    }
`endif

`endif
