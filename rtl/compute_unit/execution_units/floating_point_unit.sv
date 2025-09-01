// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "bgpu.svh"
`include "common_cells/registers.svh"

/// Floating Point Unit
// Performs floating point alu operations
module floating_point_unit import bgpu_pkg::*; #(
    /// Number of inflight instructions per warp
    parameter int unsigned NumTags = 8,
    // Width of the registers
    parameter int unsigned RegWidth = 32,
    // Number of threads in a warp
    parameter int unsigned WarpWidth = 4,
    /// Number of warps per compute unit
    parameter int unsigned NumWarps = 8,
    // Number of operands per instruction
    parameter int unsigned OperandsPerInst = 2,
    /// How many registers can each warp access as operand or destination
    parameter int unsigned RegIdxWidth = 8,
    // How many bits are used to index thread blocks inside a thread group?
    parameter int unsigned TblockIdxBits = 4,
    // Memory Address width in bits
    parameter int unsigned AddressWidth = 32,

    // Number of waiting stations
    parameter int unsigned NumFpuStations = 4,

    /// Dependent parameter, do **not** overwrite.
    parameter int unsigned TagWidth    = $clog2(NumTags),
    parameter int unsigned WidWidth = NumWarps > 1 ? $clog2(NumWarps) : 1,
    parameter type warp_data_t  = logic [RegWidth * WarpWidth-1:0],
    parameter type reg_idx_t    = logic [         RegIdxWidth-1:0],
    parameter type iid_t        = logic [   TagWidth+WidWidth-1:0],
    parameter type addr_t       = logic [        AddressWidth-1:0],
    parameter type tblock_idx_t = logic [       TblockIdxBits-1:0],
    parameter type act_mask_t   = logic [           WarpWidth-1:0]
) (
    // Clock and reset
    input logic clk_i,
    input logic rst_ni,

    // Testmode
    input logic testmode_i,

    // From Operand Collector
    output logic         eu_to_opc_ready_o,
    input  logic         opc_to_eu_valid_i,
    input  iid_t         opc_to_eu_tag_i,
    input  act_mask_t    opc_to_eu_act_mask_i,
    input  fpu_subtype_e opc_to_eu_inst_sub_i,
    input  reg_idx_t     opc_to_eu_dst_i,
    input  warp_data_t   [OperandsPerInst-1:0] opc_to_eu_operands_i,

    // To Result Collector
    input  logic       rc_to_eu_ready_i,
    output logic       eu_to_rc_valid_o,
    output act_mask_t  eu_to_rc_act_mask_o,
    output iid_t       eu_to_rc_tag_o,
    output reg_idx_t   eu_to_rc_dst_o,
    output warp_data_t eu_to_rc_data_o
);
    // #######################################################################################
    // # Local Parameters                                                                    #
    // #######################################################################################

    localparam fpnew_pkg::fpu_implementation_t FpnewImplementation = '{
        PipeRegs:   '{default: 0},
        UnitTypes:  '{
                        '{default: fpnew_pkg::MERGED},   // ADDMUL
                        '{default: fpnew_pkg::DISABLED}, // DIVSQRT
                        '{default: fpnew_pkg::PARALLEL}, // NONCOMP
                        '{default: fpnew_pkg::MERGED}    // CONV
                    },
        PipeConfig: fpnew_pkg::BEFORE
    };

    localparam fpnew_pkg::fpu_features_t FpnewFeatures = '{
        Width:         32,
        EnableVectors: 1'b0,
        EnableNanBox:  1'b1,
        FpFmtMask:     'd1 << fpnew_pkg::FP32,
        IntFmtMask:    'd1 << fpnew_pkg::INT32
    };

    localparam int unsigned FpuStationIdxWidth = NumFpuStations > 1 ? $clog2(NumFpuStations) : 1;

    // #######################################################################################
    // # Type Definitions                                                                    #
    // #######################################################################################

    typedef logic [FpuStationIdxWidth-1:0] fpu_station_idx_t;

    typedef logic      [ RegWidth-1:0] reg_data_t;
    typedef reg_data_t [WarpWidth-1:0] reg_data_per_thread_t;

    typedef struct packed {
        iid_t       tag;
        reg_idx_t   dst;
        warp_data_t data;
        act_mask_t  act_mask;
    } eu_to_opc_t;

    typedef struct packed {
        iid_t       tag;
        reg_idx_t   dst;
        act_mask_t  act_mask;
        logic [WarpWidth-1:0] result_ready;
        reg_data_per_thread_t results;
    } station_entry_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    reg_data_per_thread_t [OperandsPerInst-1:0] operands;

    logic           [NumFpuStations-1:0] fpu_stations_valid_d, fpu_stations_valid_q;
    station_entry_t [NumFpuStations-1:0] fpu_stations_d,       fpu_stations_q;

    // FPU signals
    logic             [WarpWidth-1:0] fpnew_valid_in,  fpnew_ready_in;
    logic             [WarpWidth-1:0] fpnew_valid_out, fpnew_ready_out;
    fpu_station_idx_t [WarpWidth-1:0] fpnew_tag_out;
    reg_data_t        [WarpWidth-1:0] fpnew_result;

    fpu_station_idx_t fpnew_tag_in;

    logic fpnew_op_mod;

    fpnew_pkg::roundmode_e  fpnew_rnd_mode;
    fpnew_pkg::operation_e  fpnew_op;
    fpnew_pkg::fp_format_e  fpnew_src_fmt;
    fpnew_pkg::fp_format_e  fpnew_dst_fmt;
    fpnew_pkg::int_format_e fpnew_int_fmt;

    // #######################################################################################
    // # Combinational Logic                                                                 #
    // #######################################################################################

    // Extract operands
    for (genvar i = 0; i < OperandsPerInst; i++) begin : gen_extract_operands
        assign operands[i] = opc_to_eu_operands_i[i];
    end : gen_extract_operands

    // Decode Operation into FPnew operation
    always_comb begin : decode_operation
        // Default values
        fpnew_rnd_mode = fpnew_pkg::RTZ;
        fpnew_op       = fpnew_pkg::ADD;
        fpnew_op_mod   = 1'b0;
        fpnew_src_fmt  = fpnew_pkg::FP32;
        fpnew_dst_fmt  = fpnew_pkg::FP32;
        fpnew_int_fmt  = fpnew_pkg::INT32;

        // Check instruction subtype and perform operation
        case (opc_to_eu_inst_sub_i)
            FPU_ADD: begin
                fpnew_op = fpnew_pkg::ADD;
            end
            FPU_INT_TO_FP: begin
                fpnew_op = fpnew_pkg::I2F;
            end
            FPU_FP_TO_INT: begin
                fpnew_op = fpnew_pkg::F2I;
            end
            default: begin
                `ifndef SYNTHESIS
                if (opc_to_eu_valid_i)
                    $fatal(1, "Instruction subtype not implemented: %0h", opc_to_eu_inst_sub_i);
                `endif
            end
        endcase
    end : decode_operation

    // Waiting station logic
    always_comb begin : waiting_station_logic
        // Default
        fpu_stations_d       = fpu_stations_q;
        fpu_stations_valid_d = fpu_stations_valid_q;
    end : waiting_station_logic

    // #######################################################################################
    // # Floating Point Units                                                                #
    // #######################################################################################

    for (genvar i = 0; i < WarpWidth; i++) begin : gen_fpu_units
        // Instantiate one FPU per thread in the warp
        fpnew_top #(
            .Features      ( FpnewFeatures       ),
            .Implementation( FpnewImplementation ),
            .DivSqrtSel    ( fpnew_pkg::PULP     ),
            .TagType       ( fpu_station_idx_t   ),
            .TrueSIMDClass ( 0                   ),
            .EnableSIMDMask( 0                   )
        ) i_fpnew (
            .clk_i ( clk_i  ),
            .rst_ni( rst_ni ),

            .operands_i    ( {{RegWidth{1'b0}}, operands[1][i], operands[0][i]} ),
            .rnd_mode_i    ( fpnew_rnd_mode ),
            .op_i          ( fpnew_op       ),
            .op_mod_i      ( fpnew_op_mod   ),
            .src_fmt_i     ( fpnew_src_fmt  ),
            .dst_fmt_i     ( fpnew_dst_fmt  ),
            .int_fmt_i     ( fpnew_int_fmt  ),
            .tag_i         ( fpnew_tag_in   ),
            .vectorial_op_i( 1'b0           ),
            .simd_mask_i   ( '1             ),

            .in_valid_i( fpnew_valid_in[i] ),
            .in_ready_o( fpnew_ready_in[i] ),
            .flush_i   ( 1'b0              ),

            .out_valid_o( fpnew_valid_out[i] ),
            .out_ready_i( fpnew_ready_out[i] ),
            .result_o   ( fpnew_result   [i] ),
            .tag_o      ( fpnew_tag_out  [i] ),
            .status_o   ( /* Not used */     ),

            .busy_o( /* Not used */ )
        );
    end : gen_fpu_units

    // #######################################################################################
    // # Sequential Logic                                                                    #
    // #######################################################################################

    `FF(fpu_stations_q,       fpu_stations_d,      '0, clk_i, rst_ni)
    `FF(fpu_stations_valid_q, fpu_stations_valid_d,'0, clk_i, rst_ni)

    // #######################################################################################
    // # Assertions                                                                          #
    // #######################################################################################

    `ifndef SYNTHESIS
        assert property (@(posedge clk_i) disable iff (!rst_ni)
            opc_to_eu_valid_i |-> opc_to_eu_inst_sub_i inside `FPU_VALID_SUBTYPES)
            else $error("Invalid instruction subtype: %0h", opc_to_eu_inst_sub_i);
    `endif

endmodule : floating_point_unit
