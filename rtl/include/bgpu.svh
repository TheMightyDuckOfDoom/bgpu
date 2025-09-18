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
    LSU_LOAD_WORD\
}

`ifndef SYNTHESIS
    // Valid subtypes for each execution unit
    `define IU_VALID_SUBTYPES {\
        IU_TID,\
        IU_WID,\
        IU_BID,\
        IU_TBID,\
        IU_DPA,\
        IU_ADD,\
        IU_SUB,\
        IU_AND,\
        IU_OR,\
        IU_XOR,\
        IU_SHL,\
        IU_LDI,\
        IU_ADDI,\
        IU_SUBI,\
        IU_SHLI\
    }

    `define FPU_VALID_SUBTYPES {\
        FPU_ADD,\
        FPU_INT_TO_FP,\
        FPU_FP_TO_INT,\
        FPU_SUB,\
        FPU_MUL,\
        FPU_DIV,\
        FPU_RECIP\
    }

    // JMP and SYNC never reach the BRU, as they are handled by the decoder
    `define BRU_VALID_SUBTYPES {\
        BRU_BEZ,\
        BRU_BNZ\
    }
`endif
