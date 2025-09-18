// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

package bgpu_pkg;

typedef enum logic [1:0] {
    EU_IU  = 'd0,
    EU_LSU = 'd1,
    EU_BRU = 'd2,
    EU_FPU = 'd3
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
    IU_SHL  = 'h0A, // Shift left logical

    IU_LDI  = 'h0B, // Load immediate -> concatenate operands register index
    IU_ADDI = 'h0C, // Add immediate -> add immediate value to first operand
    IU_SUBI = 'h0D, // Subtract immediate -> subtract immediate value from first operand
    IU_SHLI = 'h0E  // Shift left logical immediate
} iu_subtype_e;

typedef enum logic [5:0] {
    FPU_ADD       = 'h00, // Add operands
    FPU_INT_TO_FP = 'h01, // Convert integer to floating point
    FPU_FP_TO_INT = 'h02, // Convert floating point to integer
    FPU_SUB       = 'h03, // Subtract operands
    FPU_MUL       = 'h04, // Multiply operands
    FPU_DIV       = 'h05, // Divide operands
    FPU_RECIP     = 'h06  // Compute reciprocal of operand
} fpu_subtype_e;

typedef enum logic [5:0] {
    LSU_LOAD_BYTE  = 'h00, // Load from memory
    LSU_LOAD_HALF  = 'h01, // Load half-word from memory
    LSU_LOAD_WORD  = 'h02, // Load word from memory
    LSU_STORE_BYTE = 'h03, // Store byte to memory
    LSU_STORE_HALF = 'h04, // Store half-word to memory
    LSU_STORE_WORD = 'h05  // Store word to memory
} lsu_subtype_e;

typedef enum logic [5:0] {
    BRU_JMP  = 'h00, // Jump to address
    BRU_SYNC = 'h01, // Blocks until all threads have reached this instruction
    BRU_BNZ  = 'h02, // Branch if not zero
    BRU_BEZ  = 'h03  // Branch if zero
} bru_subtype_e;

typedef union packed {
    iu_subtype_e  iu;
    lsu_subtype_e lsu;
    bru_subtype_e bru;
    fpu_subtype_e fpu;
} inst_subtype_t;

typedef struct packed {
    eu_e           eu;
    inst_subtype_t subtype;
} inst_t;

endpackage : bgpu_pkg
