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

    IU_ADD = 'h04, // Add operands
    IU_SUB = 'h05, // Subtract operands
    IU_AND = 'h06, // Bitwise AND operands
    IU_OR  = 'h07, // Bitwise OR operands
    IU_XOR = 'h08, // Bitwise XOR operands
    IU_SHL = 'h09, // Shift left logical
    IU_SHR = 'h0A, // Shift right logical
    IU_MUL = 'h0B, // Multiply operands

    IU_LDI  = 'h0C, // Load immediate -> concatenate operands register index
    IU_ADDI = 'h0D, // Add immediate -> add immediate value to first operand
    IU_SUBI = 'h0E, // Subtract immediate -> subtract immediate value from first operand
    IU_ANDI = 'h0F, // AND immediate -> AND immediate value with first operand
    IU_ORI  = 'h10, // OR immediate -> OR immediate value with first
    IU_XORI = 'h11, // XOR immediate -> XOR immediate value with first operand
    IU_SHLI = 'h12, // Shift left logical immediate
    IU_SHRI = 'h13, // Shift right logical immediate
    IU_MULI = 'h14, // Multiply immediate -> multiply first operand with immediate value

    IU_CMPLT  = 'h15, // Compare less than
    IU_CMPLTI = 'h16, // Compare less than immediate
    IU_CMPNE  = 'h17, // Compare not equal
    IU_CMPNEI = 'h18, // Compare not equal immediate

    IU_MAX  = 'h19, // Maximum of operands
    IU_DIV  = 'h1A, // Divide operands
    IU_DIVI = 'h1B  // Divide immediate -> divide first operand by immediate value
} iu_subtype_e;

typedef enum logic [5:0] {
    FPU_ADD       = 'h00, // Add operands
    FPU_SUB       = 'h01, // Subtract operands
    FPU_MUL       = 'h02, // Multiply operands
    FPU_MAX       = 'h03, // Maximum of operands
    FPU_EXP2      = 'h04, // Compute 2^operand
    FPU_LOG2      = 'h05, // Compute log2(operand)
    FPU_RECIP     = 'h06, // Compute reciprocal of operand
    FPU_CMPLT     = 'h07, // Compare less than
    FPU_DIV       = 'h08, // Divide operands
    FPU_INT_TO_FP = 'h09, // Convert integer to floating point
    FPU_FP_TO_INT = 'h0A  // Convert floating point to integer
} fpu_subtype_e;

typedef enum logic [5:0] {
    LSU_LOAD_BYTE  = 'h00, // Load from memory
    LSU_LOAD_HALF  = 'h01, // Load half-word from memory
    LSU_LOAD_WORD  = 'h02, // Load word from memory
    LSU_STORE_BYTE = 'h03, // Store byte to memory
    LSU_STORE_HALF = 'h04, // Store half-word to memory
    LSU_STORE_WORD = 'h05, // Store word to memory
    LSU_LOAD_PARAM = 'h06  // Load word parameter
} lsu_subtype_e;

typedef enum logic [5:0] {
    BRU_BNZ  = 'h00, // Branch if not zero
    BRU_BEZ  = 'h01, // Branch if zero
    BRU_SYNC = 'h02, // Blocks until all threads have reached this instruction
    BRU_JMP  = 'h03, // Jump to address

    BRU_STOP = 6'b111111 // Stop the warp
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
