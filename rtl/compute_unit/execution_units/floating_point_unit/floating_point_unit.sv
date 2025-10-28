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

    /// Latency of the FMA Unit
    parameter int unsigned FmaLatency = 5,
    /// Latency of the Divider Unit
    parameter int unsigned DivLatency = 12,
    /// Latency of the INT2FP Unit
    parameter int unsigned Int2FpLatency = 2,
    /// Latency of the FP2INT Unit
    parameter int unsigned Fp2IntLatency = 1,

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

    function static int unsigned max(input int unsigned a, input int unsigned b);
        if (a > b)
            return a;
        else
            return b;
    endfunction

    // Should be more than the max latency of an FPU operation
    localparam int unsigned NumFpuStations = max(max(FmaLatency, DivLatency),
                                                 max(Int2FpLatency, Fp2IntLatency)) + 2;

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

    logic [NumFpuStations-1:0] fpu_station_ready, fpu_station_free;

    fpu_station_idx_t fpu_tag_in;

    // FMA Signals
    logic      [WarpWidth-1:0] fma_valid_in;
    reg_data_t [WarpWidth-1:0] fma_operand_a, fma_operand_b, fma_operand_c;
    logic                      fma_negate_a,  fma_negate_c;

    logic             [WarpWidth-1:0] fma_valid_out;
    fpu_station_idx_t [WarpWidth-1:0] fma_tag_out;
    reg_data_t        [WarpWidth-1:0] fma_result;

    // Divider Signals
    logic             [WarpWidth-1:0] fdiv_valid_in;
    reg_data_t        [WarpWidth-1:0] fdiv_operand_a, fdiv_operand_b;
    logic             [WarpWidth-1:0] fdiv_valid_out;
    fpu_station_idx_t [WarpWidth-1:0] fdiv_tag_out;
    reg_data_t        [WarpWidth-1:0] fdiv_result;

    // Converions Signals
    logic              [WarpWidth-1:0] int_to_fp_valid_in,  fp_to_int_valid_in;
    logic              [WarpWidth-1:0] int_to_fp_valid_out, fp_to_int_valid_out;
    reg_data_t         [WarpWidth-1:0] int_to_fp_result,    fp_to_int_result;
    fpu_station_idx_t  [WarpWidth-1:0] int_to_fp_tag_out,   fp_to_int_tag_out;

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
        fma_valid_in       = '0;
        fdiv_valid_in      = '0;
        int_to_fp_valid_in = '0;
        fp_to_int_valid_in = '0;

        // Default: (op1 * op2) + op3
        fma_operand_a = operands[0];
        fma_operand_b = operands[1];
        fma_operand_c = operands[1];
        fma_negate_a = 1'b0;
        fma_negate_c = 1'b0;

        // Default: op1 / op2
        fdiv_operand_a = operands[0];
        fdiv_operand_b = operands[1];

        // Check instruction subtype and perform operation
        case (opc_to_eu_inst_sub_i)
            FPU_ADD: begin
                if (opc_to_eu_valid_i && eu_to_opc_ready_o)
                    fma_valid_in = opc_to_eu_act_mask_i;

                // (op1 * 1.0) + op2
                fma_operand_b = {WarpWidth{32'h3f800000}}; // 1.0f
            end
            FPU_SUB: begin
                if (opc_to_eu_valid_i && eu_to_opc_ready_o)
                    fma_valid_in = opc_to_eu_act_mask_i;

                // (op1 * 1.0) - op2
                fma_negate_c  = 1'b1;
                fma_operand_b = {WarpWidth{32'h3f800000}}; // 1.0f
            end
            FPU_MUL: begin
                if (opc_to_eu_valid_i && eu_to_opc_ready_o)
                    fma_valid_in = opc_to_eu_act_mask_i;

                // (op1 * op2) + 0.0
                fma_operand_c = {WarpWidth{32'h00000000}}; // 0.0f
            end
            FPU_DIV: begin
                if (opc_to_eu_valid_i && eu_to_opc_ready_o)
                    fdiv_valid_in = opc_to_eu_act_mask_i;
            end
            FPU_RECIP: begin
                if (opc_to_eu_valid_i && eu_to_opc_ready_o)
                    fdiv_valid_in = opc_to_eu_act_mask_i;

                // 1.0 / op1
                fdiv_operand_a = {WarpWidth{32'h3f800000}}; // 1.0f
                fdiv_operand_b = operands[0];
            end
            FPU_INT_TO_FP: begin
                if (opc_to_eu_valid_i && eu_to_opc_ready_o)
                    int_to_fp_valid_in = opc_to_eu_act_mask_i;
            end
            FPU_FP_TO_INT: begin
                if (opc_to_eu_valid_i && eu_to_opc_ready_o)
                    fp_to_int_valid_in = opc_to_eu_act_mask_i;
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

    // We are ready for a new operations, if not all stations are valid
    assign eu_to_opc_ready_o = !(&fpu_stations_valid_q);

    // Waiting station logic
    always_comb begin : waiting_station_logic
        // Default
        fpu_stations_d       = fpu_stations_q;
        fpu_stations_valid_d = fpu_stations_valid_q;

        fpu_tag_in = '0;

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
                    fpu_tag_in = i[FpuStationIdxWidth-1:0];

                    // Input handshake
                    if (eu_to_opc_ready_o) begin
                        // Mark station as valid
                        fpu_stations_valid_d[i]        = 1'b1;
                    end
                    break;
                end
            end
        end : insert_new_instruction

        // New results
        for (int unsigned i = 0; i < WarpWidth; i++) begin : handle_fpu_results
            if (fma_valid_out[i]) begin
                // Use tag to index into stations
                fpu_stations_d[fma_tag_out[i]].results     [i] = fma_result[i];
                fpu_stations_d[fma_tag_out[i]].result_ready[i] = 1'b1;
            end

            if (fdiv_valid_out[i]) begin
                // Use tag to index into stations
                fpu_stations_d[fdiv_tag_out[i]].results     [i] = fdiv_result[i];
                fpu_stations_d[fdiv_tag_out[i]].result_ready[i] = 1'b1;
            end

            if (int_to_fp_valid_out[i]) begin
                // Use tag to index into stations
                fpu_stations_d[int_to_fp_tag_out[i]].results     [i] = int_to_fp_result[i];
                fpu_stations_d[int_to_fp_tag_out[i]].result_ready[i] = 1'b1;
            end

            if (fp_to_int_valid_out[i]) begin
                // Use tag to index into stations
                fpu_stations_d[fp_to_int_tag_out[i]].results     [i] = fp_to_int_result[i];
                fpu_stations_d[fp_to_int_tag_out[i]].result_ready[i] = 1'b1;
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

        .req_o ( eu_to_rc_valid_o       ),
        .gnt_i ( rc_to_eu_ready_i       ),
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
    // # FMA Units                                                                           #
    // #######################################################################################

    for (genvar i = 0; i < WarpWidth; i++) begin : gen_fma_units
        // Instantiate one FMA per thread in the warp
        fma #(
            .DataWidth( RegWidth          ),
            .Latency  ( FmaLatency        ),
            .tag_t    ( fpu_station_idx_t )
        ) i_fma (
            .clk_i ( clk_i  ),
            .rst_ni( rst_ni ),

            .valid_i    ( fma_valid_in[i]  ),
            .tag_i      ( fpu_tag_in       ),
            .negate_a_i ( fma_negate_a     ),
            .negate_c_i ( fma_negate_c     ),
            .operand_a_i( fma_operand_a[i] ),
            .operand_b_i( fma_operand_b[i] ),
            .operand_c_i( fma_operand_c[i] ),

            .valid_o ( fma_valid_out[i] ),
            .tag_o   ( fma_tag_out  [i] ),
            .result_o( fma_result   [i] )
        );
    end : gen_fma_units

    // #######################################################################################
    // # Divider Units                                                                       #
    // #######################################################################################

    for (genvar i = 0; i < WarpWidth; i++) begin : gen_div_units
        // Instantiate one Divider per thread in the warp
        fop #(
            .DataWidth( RegWidth          ),
            .Operation( "DIV"             ),
            .Latency  ( DivLatency        ),
            .tag_t    ( fpu_station_idx_t )
        ) i_div (
            .clk_i ( clk_i  ),
            .rst_ni( rst_ni ),

            .valid_i    ( fdiv_valid_in[i]  ),
            .tag_i      ( fpu_tag_in        ),
            .operand_a_i( fdiv_operand_a[i] ),
            .operand_b_i( fdiv_operand_b[i] ),

            .valid_o ( fdiv_valid_out[i] ),
            .tag_o   ( fdiv_tag_out  [i] ),
            .result_o( fdiv_result   [i] )
        );
    end : gen_div_units

    // #######################################################################################
    // # Int to FP Units                                                                     #
    // #######################################################################################

    for (genvar i = 0; i < WarpWidth; i++) begin : gen_int2fp_units
        // Instantiate one Int2FP per thread in the warp
        int_to_fp #(
            .DataWidth( RegWidth          ),
            .Latency  ( Int2FpLatency     ),
            .tag_t    ( fpu_station_idx_t )
        ) i_int2fp (
            .clk_i ( clk_i  ),
            .rst_ni( rst_ni ),

            .valid_i( int_to_fp_valid_in[i] ),
            .tag_i  ( fpu_tag_in            ),
            .int_i  ( operands[0][i]        ),

            .valid_o( int_to_fp_valid_out[i] ),
            .tag_o  ( int_to_fp_tag_out  [i] ),
            .fp_o   ( int_to_fp_result   [i] )
        );
    end : gen_int2fp_units

    // #######################################################################################
    // # FP to Int Units                                                                     #
    // #######################################################################################

    for (genvar i = 0; i < WarpWidth; i++) begin : gen_fp2int_units
        // Instantiate one Int2FP per thread in the warp
        fp_to_int #(
            .DataWidth( RegWidth          ),
            .Latency  ( Fp2IntLatency     ),
            .tag_t    ( fpu_station_idx_t )
        ) i_fp2int (
            .clk_i ( clk_i  ),
            .rst_ni( rst_ni ),

            .valid_i( fp_to_int_valid_in[i] ),
            .tag_i  ( fpu_tag_in            ),
            .fp_i   ( operands[0][i]        ),

            .valid_o( fp_to_int_valid_out[i] ),
            .tag_o  ( fp_to_int_tag_out  [i] ),
            .int_o  ( fp_to_int_result   [i] )
        );
    end : gen_fp2int_units

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
