// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "bgpu/instructions.svh"

/// Register and Operand Collector Stage
module register_opc_stage #(
    /// Number of inflight instructions per warp
    parameter int unsigned NumTags = 8,
    /// Width of the Program Counter
    parameter int unsigned PcWidth = 32,
    /// Number of warps per compute unit
    parameter int unsigned NumWarps = 8,
    /// Number of threads per warp
    parameter int unsigned WarpWidth = 4,
    /// How many registers can each warp access as operand or destination
    parameter int unsigned RegIdxWidth = 6,
    /// How many operands each instruction can have
    parameter int unsigned OperandsPerInst = 2,
    /// How many Banks are in the register file
    parameter int unsigned NumBanks = 4,
    /// Width of a singled register
    parameter int unsigned RegWidth = 32,
    /// Should the register file banks be dual port?
    parameter bit DualPortRegisterBanks = 1'b0,
    /// Number of operand collectors
    parameter int unsigned NumOperandCollectors = 6,

    /// Dependent parameter, do **not** overwrite.
    parameter int unsigned TagWidth    = $clog2(NumTags),
    parameter int unsigned WidWidth    = NumWarps > 1 ? $clog2(NumWarps) : 1,
    parameter type         wid_t       = logic [            WidWidth-1:0],
    parameter type         reg_idx_t   = logic [         RegIdxWidth-1:0],
    parameter type         pc_t        = logic [             PcWidth-1:0],
    parameter type         act_mask_t  = logic [           WarpWidth-1:0],
    parameter type         warp_data_t = logic [RegWidth * WarpWidth-1:0],
    parameter type         iid_t       = logic [   TagWidth+WidWidth-1:0]
) (
    /// Clock and Reset
    input  logic clk_i,
    input  logic rst_ni,

    /// From Multi Warp Dispatcher
    output logic       opc_ready_o,
    input  logic       disp_valid_i,
    input  iid_t       disp_tag_i,
    input  pc_t        disp_pc_i,
    input  act_mask_t  disp_act_mask_i,
    input  bgpu_inst_t disp_inst_i,
    input  reg_idx_t   disp_dst_i,
    input  logic       [OperandsPerInst-1:0] disp_src_required_i,
    input  reg_idx_t   [OperandsPerInst-1:0] disp_src_i,

    /// To Execution Units
    output logic       opc_valid_o,
    input  logic       eu_ready_i,
    output iid_t       opc_tag_o,
    output pc_t        opc_pc_o,
    output act_mask_t  opc_act_mask_o,
    output bgpu_inst_t opc_inst_o,
    output reg_idx_t   opc_dst_o,
    output warp_data_t [OperandsPerInst-1:0] opc_operand_data_o,

    /// From Execution Units
    output logic       opc_to_eu_ready_o,
    input  logic       eu_valid_i,
    input  iid_t       eu_tag_i,
    input  reg_idx_t   eu_dst_i,
    input  warp_data_t eu_data_i
);
    // #######################################################################################
    // # Local Parameters                                                                    #
    // #######################################################################################

    localparam int unsigned TotalNumRegisters  = (NumWarps * 2**RegIdxWidth);
    localparam int unsigned RegistersPerBank   = TotalNumRegisters / NumBanks;
    localparam int unsigned BankRegAddrWidth   = RegistersPerBank > 1
                                                    ? $clog2(RegistersPerBank) : 1;
    localparam int unsigned NumOPCRequestPorts = NumOperandCollectors * OperandsPerInst;
    localparam int unsigned OpcTagWidth        = NumOPCRequestPorts > 1
                                                    ? $clog2(NumOPCRequestPorts) : 1;
    localparam int unsigned BankSelWidth       = NumBanks > 1 ? $clog2(NumBanks) : 1;

    // #######################################################################################
    // # Typedefs                                                                            #
    // #######################################################################################

    typedef logic [     OpcTagWidth-1:0] opc_tag_t;
    typedef logic [    BankSelWidth-1:0] bank_sel_t;
    typedef logic [BankRegAddrWidth-1:0] bank_reg_addr_t;

    // Ready instruction from Operand Collector to Execution Unit
    typedef struct packed {
        iid_t       tag;       // Instruction ID
        pc_t        pc;        // Program Counter
        act_mask_t  act_mask;  // Activation Mask
        bgpu_inst_t inst;      // Instruction
        reg_idx_t   dst;       // Destination Register Index
        warp_data_t [OperandsPerInst-1:0] operands; // Operands Data
    } opc_inst_t;

    typedef struct packed {
        bank_reg_addr_t addr; // Address in the bank
        warp_data_t     data; // Data to write
    } bank_write_req_t;

    // #######################################################################################
    // # Signals                                                                            #
    // #######################################################################################

    /// Operand Collectors
    // Insert instruction valid and ready per Operand Collector
    logic [NumOperandCollectors-1:0] opc_insert_valid, opc_insert_ready;

    // Read Request
    logic     [NumOPCRequestPorts-1:0] opc_read_req_valid;
    logic     [NumOPCRequestPorts-1:0] opc_read_req_ready;
    wid_t     [NumOPCRequestPorts-1:0] opc_read_req_wid;
    reg_idx_t [NumOPCRequestPorts-1:0] opc_read_req_reg_idx;

    // Read WID+REG_IDX to Bank Selection and Register Address
    bank_sel_t      [NumOPCRequestPorts-1:0] opc_read_req_bank_sel;
    bank_reg_addr_t [NumOPCRequestPorts-1:0] opc_read_req_addr;

    // Write WID+REG_IDX to Bank Selection and Register Address
    bank_sel_t       eu_write_req_bank_sel;
    bank_write_req_t eu_write_req;

    // Read Response
    logic       [NumOPCRequestPorts-1:0] opc_read_rsp_valid;
    warp_data_t [NumOPCRequestPorts-1:0] opc_read_rsp_data;

    // Read Response to Execution Units
    logic      [NumOperandCollectors-1:0] opc_eu_valid, opc_eu_ready;
    opc_inst_t [NumOperandCollectors-1:0] opc_eu_inst;
    opc_inst_t                            selected_opc_inst;

    /// Register File Banks
    // Write port
    logic            [NumBanks-1:0] banks_write_req_valid;
    logic            [NumBanks-1:0] banks_write_req_ready;
    bank_write_req_t [NumBanks-1:0] banks_write_req;

    // Read Request Interconnect to Register Banks Read Ports
    logic           [NumBanks-1:0] banks_read_req_valid;
    logic           [NumBanks-1:0] banks_read_req_ready;
    bank_reg_addr_t [NumBanks-1:0] banks_read_req_addr;
    opc_tag_t       [NumBanks-1:0] banks_read_req_tag;

    // Register Banks Read Response to Read Response Interconnect
    logic       [NumBanks-1:0] banks_read_rsp_valid;
    logic       [NumBanks-1:0] banks_read_rsp_ready;
    opc_tag_t   [NumBanks-1:0] banks_read_rsp_tag;
    warp_data_t [NumBanks-1:0] banks_read_rsp_data;

    // #######################################################################################
    // # Read Request Interconnect between Operand Collectors and Register Banks             #
    // #######################################################################################

    for(genvar i = 0; i < NumOPCRequestPorts; i++) begin : gen_read_indexer
        register_indexer #(
            .NumWarps        ( NumWarps         ),
            .RegIdxWidth     ( RegIdxWidth      ),
            .NumBanks        ( NumBanks         ),
            .RegistersPerBank( RegistersPerBank )
        ) i_read_request_indexer (
            // Inputs
            .wid_i    ( opc_read_req_wid    [i] ),
            .reg_idx_i( opc_read_req_reg_idx[i] ),

            // Outputs
            .bank_sel_o     ( opc_read_req_bank_sel[i] ),
            .bank_reg_addr_o( opc_read_req_addr    [i] )
        );
    end : gen_read_indexer

    // Each Operand Collector has OperandsPerInst request ports
    stream_xbar #(
        .NumInp     ( NumOPCRequestPorts ),
        .NumOut     ( NumBanks           ),
        .payload_t  ( bank_reg_addr_t    ),
        .OutSpillReg( 1'b0               ),
        .ExtPrio    ( 1'b0               ),
        .AxiVldRdy  ( 1'b0               ),
        .LockIn     ( 1'b0               ),
        .AxiVldMask ( '1                 )
    ) i_read_request_interconnect (
        .clk_i  ( clk_i  ),
        .rst_ni ( rst_ni ),

        // Request ports |-> from Operand Collectors Read Request ports
        .data_i ( opc_read_req_addr     ),
        .sel_i  ( opc_read_req_bank_sel ),
        .valid_i( opc_read_req_valid    ),
        .ready_o( opc_read_req_ready    ),

        // Grant ports |-> to Register Banks Read Ports
        .data_o ( banks_read_req_addr  ),
        .idx_o  ( banks_read_req_tag   ),
        .valid_o( banks_read_req_valid ),
        .ready_i( banks_read_req_ready ),

        // Tie-Offs
        .flush_i( 1'b0 ),
        .rr_i   ( '0   )
    );

    // #######################################################################################
    // # Read Response Interconnect between Register Banks and Operand Collectors            #
    // #######################################################################################

    stream_xbar #(
        .NumInp     ( NumBanks           ),
        .NumOut     ( NumOPCRequestPorts ),
        .payload_t  ( warp_data_t             ),
        .OutSpillReg( 1'b0               ),
        .ExtPrio    ( 1'b0               ),
        .AxiVldRdy  ( 1'b0               ),
        .LockIn     ( 1'b0               ),
        .AxiVldMask ( '1                 )
    ) i_read_response_interconnect (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        // Request ports |-> from Register Banks Read Ports
        .data_i ( banks_read_rsp_data  ),
        .sel_i  ( banks_read_rsp_tag   ),
        .valid_i( banks_read_rsp_valid ),
        .ready_o( banks_read_rsp_ready ),

        // Grant ports |-> to Operand Collectors
        .data_o ( opc_read_rsp_data  ),
        .valid_o( opc_read_rsp_valid ),

        // Tie-Offs
        .flush_i( 1'b0         ),
        .rr_i   ( '0           ),
        .ready_i( '1           ),
        .idx_o  ( /* UNUSED */ )
    );

    // #######################################################################################
    // # Write Request Interconnect between Execution Units and Register Banks               #
    // #######################################################################################

    register_indexer #(
        .NumWarps        ( NumWarps         ),
        .RegIdxWidth     ( RegIdxWidth      ),
        .NumBanks        ( NumBanks         ),
        .RegistersPerBank( RegistersPerBank )
    ) i_write_request_indexer (
        // Inputs
        .wid_i     ( eu_tag_i[WidWidth-1:0] ),
        .reg_idx_i ( eu_dst_i               ),

        // Outputs
        .bank_sel_o     ( eu_write_req_bank_sel  ),
        .bank_reg_addr_o( eu_write_req.addr      )
    );

    assign eu_write_req.data = eu_data_i;

    stream_xbar #(
        .NumInp     ( 1                ),
        .NumOut     ( NumBanks         ),
        .payload_t  ( bank_write_req_t ),
        .OutSpillReg( 1'b0             ),
        .ExtPrio    ( 1'b0             ),
        .AxiVldRdy  ( 1'b0             ),
        .LockIn     ( 1'b0             ),
        .AxiVldMask ( '1               )
    ) i_write_request_interconnect (
        .clk_i  ( clk_i  ),
        .rst_ni ( rst_ni ),

        // Request ports |-> from Execution Units
        .data_i ( eu_write_req          ),
        .sel_i  ( eu_write_req_bank_sel ),
        .valid_i( eu_valid_i            ),
        .ready_o( opc_to_eu_ready_o     ),

        // Grant ports |-> to Register Banks Write Ports
        .data_o ( banks_write_req       ),
        .valid_o( banks_write_req_valid ),
        .ready_i( banks_write_req_ready ),

        // Tie-Offs
        .flush_i( 1'b0         ),
        .rr_i   ( '0           ),
        .idx_o  ( /* UNUSED */ )
    );

    // #######################################################################################
    // # Register File Banks                                                                 #
    // #######################################################################################

    // Register Banks are each RegWidth wide |-> store a register for a full warp
    for(genvar i = 0; i < NumBanks; i++) begin : gen_register_banks
        register_file_bank #(
            .DataWidth   ( RegWidth * WarpWidth  ),
            .NumRegisters( RegistersPerBank      ),
            .DualPort    ( DualPortRegisterBanks ),
            .tag_t       ( opc_tag_t             )
        ) i_register_file_bank (
            .clk_i ( clk_i  ),
            .rst_ni( rst_ni ),

            // Write port
            .write_valid_i( banks_write_req_valid[i]      ),
            .write_addr_i ( banks_write_req      [i].addr ),
            .write_data_i ( banks_write_req      [i].data ),
            .write_ready_o( banks_write_req_ready[i]      ),

            // Read port
            .read_valid_i( banks_read_req_valid[i] ),
            .read_ready_o( banks_read_req_ready[i] ),
            .read_tag_i  ( banks_read_req_tag  [i] ),
            .read_addr_i ( banks_read_req_addr [i] ),

            // Read output
            .read_valid_o( banks_read_rsp_valid[i] ),
            .read_tag_o  ( banks_read_rsp_tag [i] ),
            .read_data_o ( banks_read_rsp_data [i] )
        );
    end : gen_register_banks

    // #######################################################################################
    // # Operand Collectors                                                                 #
    // #######################################################################################

    // Distribute the instruction to a ready Operand Collector
    always_comb begin : select_operand_collector_for_insert
        opc_insert_valid = '0;
        for(int i = 0; i < NumOperandCollectors; i++) begin : check_operand_collector_ready
            if (opc_insert_ready[i]) begin
                opc_insert_valid[i] = disp_valid_i;
                break;
            end
        end : check_operand_collector_ready
    end : select_operand_collector_for_insert

    // We can accpet an instruction if at least one Operand Collector is ready
    assign opc_ready_o = |opc_insert_ready;

    // Generate Operand Collectors
    for(genvar i = 0; i < NumOperandCollectors; i++) begin : gen_operand_collectors
        operand_collector #(
            .NumTags          ( NumTags            ),
            .PcWidth          ( PcWidth            ),
            .NumWarps         ( NumWarps           ),
            .WarpWidth        ( WarpWidth          ),
            .RegIdxWidth      ( RegIdxWidth        ),
            .OperandsPerInst  ( OperandsPerInst    ),
            .RegWidth         ( RegWidth           )
        ) i_operand_collector (
            .clk_i ( clk_i  ),
            .rst_ni( rst_ni ),

            // From Multi Warp Dispatcher
            .opc_ready_o        ( opc_insert_ready[i] ),
            .disp_valid_i       ( opc_insert_valid[i] ),
            .disp_tag_i         ( disp_tag_i          ),
            .disp_pc_i          ( disp_pc_i           ),
            .disp_act_mask_i    ( disp_act_mask_i     ),
            .disp_inst_i        ( disp_inst_i         ),
            .disp_dst_i         ( disp_dst_i          ),
            .disp_src_required_i( disp_src_required_i ),
            .disp_src_i         ( disp_src_i          ),

            // To Register File
            .opc_read_req_valid_o  ( opc_read_req_valid  [i*OperandsPerInst +: OperandsPerInst] ),
            .opc_read_req_wid_o    ( opc_read_req_wid    [i*OperandsPerInst +: OperandsPerInst] ),
            .opc_read_req_reg_idx_o( opc_read_req_reg_idx[i*OperandsPerInst +: OperandsPerInst] ),
            .opc_read_req_ready_i  ( opc_read_req_ready  [i*OperandsPerInst +: OperandsPerInst] ),

            // From Register File
            .opc_read_rsp_valid_i( opc_read_rsp_valid[i*OperandsPerInst +: OperandsPerInst] ),
            .opc_read_rsp_data_i ( opc_read_rsp_data [i*OperandsPerInst +: OperandsPerInst] ),

            // To Execution Units
            .eu_ready_i        ( opc_eu_ready[i]          ),
            .opc_valid_o       ( opc_eu_valid[i]          ),
            .opc_tag_o         ( opc_eu_inst [i].tag      ),
            .opc_pc_o          ( opc_eu_inst [i].pc       ),
            .opc_act_mask_o    ( opc_eu_inst [i].act_mask ),
            .opc_inst_o        ( opc_eu_inst [i].inst     ),
            .opc_dst_o         ( opc_eu_inst [i].dst      ),
            .opc_operand_data_o( opc_eu_inst [i].operands )
        );
    end : gen_operand_collectors

    // #######################################################################################
    // # Operand Collector to Execution Unit Selection                                       #
    // #######################################################################################

    // Arbitrate the output of the Operand Collectors to a single output stream
    stream_arbiter #(
        .DATA_T   ( opc_inst_t           ),
        .N_INP    ( NumOperandCollectors ),
        .ARBITER  ( "rr"                 )
    ) i_opc_to_eu_arbiter (
        .clk_i        ( clk_i             ),
        .rst_ni       ( rst_ni            ),
        .inp_data_i   ( opc_eu_inst       ),
        .inp_valid_i  ( opc_eu_valid      ),
        .inp_ready_o  ( opc_eu_ready      ),
        .oup_data_o   ( selected_opc_inst ),
        .oup_valid_o  ( opc_valid_o       ),
        .oup_ready_i  ( eu_ready_i        )
    );

    // Assign the selected instruction to the output
    assign opc_tag_o          = selected_opc_inst.tag;
    assign opc_pc_o           = selected_opc_inst.pc;
    assign opc_act_mask_o     = selected_opc_inst.act_mask;
    assign opc_inst_o         = selected_opc_inst.inst;
    assign opc_dst_o          = selected_opc_inst.dst;
    assign opc_operand_data_o = selected_opc_inst.operands;

    // #######################################################################################
    // # Assertions                                                                          #
    // #######################################################################################

    `ifndef SYNTHESIS
        // Check that the number of registers is divisible by the number of banks
        initial assert (TotalNumRegisters % NumBanks == 0) else
            $error("TotalNumRegisters %% NumBanks != 0. This is not supported.");

        // Check that each bank has at least one register
        initial assert (TotalNumRegisters >= NumBanks) else
            $error("NumBanks is greater than the total number of registers.");

        // Read Response Interconnect always has to be ready
        for(genvar i = 0; i < NumBanks; i++) begin : gen_read_response_interconnect_assertions
            assert property (@(posedge clk_i) disable iff (~rst_ni)
                (banks_read_rsp_valid[i] |-> banks_read_rsp_ready[i])) else
                $error("Read Response Interconnect is not ready for bank %0d", i);
        end : gen_read_response_interconnect_assertions
    `endif

endmodule : register_opc_stage
