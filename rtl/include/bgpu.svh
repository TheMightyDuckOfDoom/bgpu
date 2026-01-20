// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Store operations
`define INST_STORE {\
    LSU_STORE_BYTE,\
    LSU_STORE_HALF,\
    LSU_STORE_WORD\
}

// Load operations
`define INST_LOAD {\
    LSU_LOAD_BYTE,\
    LSU_LOAD_HALF,\
    LSU_LOAD_WORD,\
    LSU_LOAD_PARAM\
}

`ifndef SYNTHESIS
    // Valid subtypes for each execution unit
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
        IU_SHL,\
        IU_SHR,\
        IU_MUL,\
        IU_LDI,\
        IU_ADDI,\
        IU_SUBI,\
        IU_ANDI,\
        IU_ORI,\
        IU_XORI,\
        IU_SHLI,\
        IU_SHRI,\
        IU_MULI,\
        IU_CMPLT,\
        IU_CMPLTI,\
        IU_CMPNE,\
        IU_CMPNEI,\
        IU_MAX,\
        IU_DIV,\
        IU_DIVI\
    }

    `define FPU_VALID_SUBTYPES {\
        FPU_ADD,\
        FPU_SUB,\
        FPU_MUL,\
        FPU_MAX,\
        FPU_EXP2,\
        FPU_LOG2,\
        FPU_RECIP,\
        FPU_CMPLT,\
        FPU_DIV,\
        FPU_INT_TO_FP,\
        FPU_FP_TO_INT\
    }

    // JMP and SYNC never reach the BRU, as they are handled by the decoder
    `define BRU_VALID_SUBTYPES {\
        BRU_BNZ,\
        BRU_BEZ,\
        BRU_SYNC,\
        BRU_JMP\
    }
`endif
