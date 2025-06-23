// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

package bgpu_pkg;

typedef enum logic [1:0] {
    EU_IU  = 'd0,
    EU_LSU = 'd1
} eu_e;

typedef enum logic [5:0] {
    IU_TID  = 'h00, // Get thread ID inside a warp
    IU_WID  = 'h01, // Get warp ID
    IU_BID  = 'h02, // Get block ID
    IU_TBID = 'h03, // Get thread id inside thread block -> BID * Width + TID

    IU_DPA  = 'h04, // Get Data / Parameter Address

    IU_ADD  = 'h05, // Add operands
    IU_SUB  = 'h06, // Subtract operands
    IU_AND  = 'h07, // Bitwise AND operands
    IU_OR   = 'h08, // Bitwise OR operands
    IU_XOR  = 'h09, // Bitwise XOR operands

    IU_LDI  = 'h0A, // Load immediate -> concatenate operands register index
    IU_ADDI = 'h0B, // Add immediate -> add immediate value to first operand
    IU_SUBI = 'h0C, // Subtract immediate -> subtract immediate value from first operand

    IU_SLL  = 'h0D, // Shift left logical
    IU_SLLI = 'h0E  // Shift left logical immediate
} iu_subtype_e;

typedef enum logic [5:0] {
    LSU_LOAD_BYTE  = 'h00, // Load from memory
    LSU_LOAD_HALF  = 'h01, // Load half-word from memory
    LSU_LOAD_WORD  = 'h02, // Load word from memory
    LSU_STORE_BYTE = 'h03, // Store byte to memory
    LSU_STORE_HALF = 'h04, // Store half-word to memory
    LSU_STORE_WORD = 'h05  // Store word to memory
} lsu_subtype_e;

typedef union packed {
    iu_subtype_e  iu;
    lsu_subtype_e lsu;
} inst_subtype_t;

typedef struct packed {
    eu_e           eu;
    inst_subtype_t subtype;
} inst_t;

// Store operations
`define INST_STORE {\
    LSU_STORE_BYTE,\
    LSU_STORE_HALF,\
    LSU_STORE_WORD\
}

`define INST_LOAD {\
    LSU_LOAD_BYTE,\
    LSU_LOAD_HALF,\
    LSU_LOAD_WORD\
}

`ifndef SYNTHESIS
    `define IU_VALID_SUBTYPES {\
        IU_TID,\
        IU_WID,\
        IU_BID,\
        IU_TBID,\
        IU_ADD,\
        IU_SUB,\
        IU_AND,\
        IU_OR,\
        IU_XOR,\
        IU_LDI,\
        IU_ADDI,\
        IU_SUBI,\
        IU_SLL,\
        IU_SLLI\
    }
`endif

endpackage : bgpu_pkg
