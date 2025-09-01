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

    // Should be more than the max latency of an FPU operation
    localparam int unsigned NumFpuStations = 5;

    localparam fpnew_pkg::fpu_implementation_t FpnewImplementation = '{
        PipeRegs:   '{
                        '{default: 3}, // ADDMUL
                        '{default: 1}, // DIVSQRT
                        '{default: 1}, // NONCOMP
                        '{default: 1}  // CONV
                    },
        UnitTypes:  '{
                        '{default: fpnew_pkg::PARALLEL},   // ADDMUL
                        '{default: fpnew_pkg::DISABLED}, // DIVSQRT
                        '{default: fpnew_pkg::PARALLEL}, // NONCOMP
                        '{default: fpnew_pkg::MERGED}    // CONV
                    },
        PipeConfig: fpnew_pkg::DISTRIBUTED
    };

    localparam fpnew_pkg::fpu_features_t FpnewFeatures = '{
        Width:         32,
        EnableVectors: 1'b0,
        EnableNanBox:  1'b1,
        FpFmtMask:     {1'b1, 1'b0, 1'b0, 1'b0, 1'b0},
        IntFmtMask:    {1'b0, 1'b0, 1'b1, 1'b0}
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

    station_entry_t selected_station_entry;

    logic fpu_station_available;
    logic [NumFpuStations-1:0] fpu_station_ready, fpu_station_free;

    logic fpu_fork_ready;

    // FPU signals
    logic             [WarpWidth-1:0] fpnew_valid_in,  fpnew_ready_in;
    logic             [WarpWidth-1:0] fpnew_valid_out;
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

    // Station is ready if valid and all results are ready
    for (genvar i = 0; i < NumFpuStations; i++) begin : gen_fpu_station_ready
        assign fpu_station_ready[i] = fpu_stations_valid_q[i] && (&fpu_stations_q[i].result_ready);
    end : gen_fpu_station_ready

    // One station is free, if not all are valid
    assign fpu_station_available = !(&fpu_stations_valid_q);

    // Ready if station entry is available and FPU fork is ready
    assign eu_to_opc_ready_o = fpu_station_available && fpu_fork_ready;

    // Waiting station logic
    always_comb begin : waiting_station_logic
        // Default
        fpu_stations_d       = fpu_stations_q;
        fpu_stations_valid_d = fpu_stations_valid_q;

        fpnew_tag_in = '0;

        // Insert a new instruction
        if (opc_to_eu_valid_i) begin : insert_new_instruction
            // Find first free station
            for (int unsigned i = 0; i < NumFpuStations; i++) begin
                if (!fpu_stations_valid_q[i]) begin
                    // Assign station values
                    fpu_stations_d[i].tag      = opc_to_eu_tag_i;
                    fpu_stations_d[i].dst      = opc_to_eu_dst_i;
                    fpu_stations_d[i].act_mask = opc_to_eu_act_mask_i;
                    fpu_stations_d[i].results  = '0;

                    // Inactive threads are already ready
                    fpu_stations_d[i].result_ready = ~opc_to_eu_act_mask_i;

                    // Pass entry index as tag to FPU
                    fpnew_tag_in = i[FpuStationIdxWidth-1:0];

                    // Input handshake
                    if (eu_to_opc_ready_o) begin
                        // Mark station as valid
                        fpu_stations_valid_d[i]        = 1'b1;
                    end
                    break;
                end
            end
        end : insert_new_instruction

        // New results from FPUs
        for (int unsigned i = 0; i < WarpWidth; i++) begin : handle_fpu_results
            if (fpnew_valid_out[i]) begin
                // Use tag to index into stations
                fpu_stations_d[fpnew_tag_out[i]].results     [i] = fpnew_result[i];
                fpu_stations_d[fpnew_tag_out[i]].result_ready[i] = 1'b1;
            end
        end : handle_fpu_results

        // Free stations that are sent to the Result Collector
        for (int unsigned i = 0; i < NumFpuStations; i++) begin : free_sent_stations
            // Deallocate station entry
            if (fpu_station_free[i] && eu_to_rc_valid_o && rc_to_eu_ready_i) begin
                fpu_stations_valid_d[i] = 1'b0;
            end
        end : free_sent_stations
    end : waiting_station_logic

    // Arbiter for Result Collector
    rr_arb_tree #(
        .DataType ( station_entry_t ),
        .NumIn    ( NumFpuStations  ),
        .ExtPrio  ( 1'b0 ),
        .AxiVldRdy( 1'b0 ),
        .LockIn   ( 1'b0 ),
        .FairArb  ( 1'b1 )
    ) i_rr_arb (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .req_i ( fpu_station_ready ),
        .gnt_o ( fpu_station_free  ),
        .data_i( fpu_stations_q    ),

        .req_o ( eu_to_rc_valid_o      ),
        .gnt_i ( rc_to_eu_ready_i      ),
        .data_o( selected_station_entry ),

        // Unused
        .idx_o  ( /* NOT CONNECTED */ ),
        .flush_i( 1'b0                ),
        .rr_i   ( '0                  )
    );

    // Assign outputs to Result Collector
    assign eu_to_rc_act_mask_o = selected_station_entry.act_mask;
    assign eu_to_rc_tag_o      = selected_station_entry.tag;
    assign eu_to_rc_dst_o      = selected_station_entry.dst;
    assign eu_to_rc_data_o     = selected_station_entry.results;

    // #######################################################################################
    // # Floating Point Units                                                                #
    // #######################################################################################

    stream_fork_dynamic #(
        .N_OUP( WarpWidth )
    ) i_fpnew_fork (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        .valid_i( opc_to_eu_valid_i && fpu_station_available ),
        .ready_o( fpu_fork_ready ),

        .sel_i      ( opc_to_eu_act_mask_i ),
        .sel_valid_i( 1'b1                 ),
        .sel_ready_o( /* Not used */       ),

        .valid_o( fpnew_valid_in ),
        .ready_i( fpnew_ready_in )
    );

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

            .operands_i    ( {operands[1][i], operands[1][i], operands[0][i]} ),
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
            .out_ready_i( fpnew_valid_out[i] ),
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
