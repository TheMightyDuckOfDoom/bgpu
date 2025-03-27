// Copyright Feb-March 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Dummy Instruction Cache
/// contains a simple lookup memory, no real cache functionality
module dummy_instruction_cache #(
    /// Program size
    parameter int MemorySize = 0,
    /// Width of the Program Counter
    parameter int PcWidth = 32,
    /// Number of warps per compute unit
    parameter int NumWarps = 8,
    /// Number of threads per warp
    parameter int WarpWidth = 32,
    /// Encoded instruction width
    parameter int EncInstWidth = 32,

    /// Dependent parameter, do **not** overwrite.
    parameter int  WidWidth   = $clog2(NumWarps),
    parameter type wid_t      = logic [    WidWidth-1:0],
    parameter type pc_t       = logic [     PcWidth-1:0],
    parameter type act_mask_t = logic [   WarpWidth-1:0],
    parameter type enc_inst_t = logic [EncInstWidth-1:0]
) (
    // Write into memory
    input  logic      clk_i,
    input  logic      mem_write_i,
    input  pc_t       mem_pc_i,
    input  enc_inst_t mem_inst_i,

    // From Fetcher
    output logic      ic_ready_o,
    input  logic      fe_valid_i,
    input  pc_t       fe_pc_i,
    input  act_mask_t fe_act_mask_i,
    input  wid_t      fe_warp_id_i,

    // To Decode
    input  logic      dec_ready_i,
    output logic      ic_valid_o,
    output pc_t       ic_pc_o,
    output act_mask_t ic_act_mask_o,
    output wid_t      ic_warp_id_o,
    output enc_inst_t ic_inst_o
);
    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    enc_inst_t inst_memory [MemorySize];

    // #######################################################################################
    // # Write logic                                                                         #
    // #######################################################################################

    always_ff @(posedge clk_i) begin
        if (mem_write_i) begin
            `ifndef SYNTHSIS
                assert(mem_pc_i < MemorySize[PcWidth-1:0])
                else $error("mem_pc_i larger than memory size!");
            `endif
            inst_memory[mem_pc_i[$clog2(MemorySize)-1:0]] <= mem_inst_i;
        end
    end

    // #######################################################################################
    // # Outputs                                                                             #
    // #######################################################################################

    // Dummy instruction cache is ready to receive a new instruction if decode is ready
    assign ic_ready_o = dec_ready_i;

    // Output valid if fetecher is valid
    assign ic_valid_o = fe_valid_i;

    // Lookup instruction in memory
    assign ic_inst_o = fe_pc_i < MemorySize[PcWidth-1:0]
                            ? inst_memory[fe_pc_i[$clog2(MemorySize)-1:0]] : '0;

    // Passthrough pc, act_mask and warp_id
    assign ic_pc_o       = fe_pc_i;
    assign ic_act_mask_o = fe_act_mask_i;
    assign ic_warp_id_o  = fe_warp_id_i;

endmodule : dummy_instruction_cache
