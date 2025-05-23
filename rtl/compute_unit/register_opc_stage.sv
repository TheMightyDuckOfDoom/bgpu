// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Register and Operand Collector Stage
module register_opc_stage #(
    /// Number of inflight instructions per warp
    parameter int unsigned NumTags = 8,
    /// Width of the Program Counter
    parameter int unsigned PcWidth = 32,
    /// Number of warps per compute unit
    parameter int unsigned NumWarps = 8,
    /// Number of threads per warp
    parameter int unsigned WarpWidth = 32,
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
    parameter int unsigned NumOperandCollectors = 1,

    /// Dependent parameter, do **not** overwrite.
    parameter int unsigned TagWidth   = $clog2(NumTags),
    parameter int unsigned WidWidth   = $clog2(NumWarps),
    parameter type         wid_t      = logic [         WidWidth-1:0],
    parameter type         reg_idx_t  = logic [      RegIdxWidth-1:0],
    parameter type         pc_t       = logic [          PcWidth-1:0],
    parameter type         act_mask_t = logic [        WarpWidth-1:0],
    parameter type         tag_t      = logic [         TagWidth-1:0],
    parameter type         data_t     = logic [         RegWidth-1:0],
    parameter type         iid_t      = logic [TagWidth+WidWidth-1:0]
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
    input  reg_idx_t   disp_dst_i,
    input  reg_idx_t  [OperandsPerInst-1:0] disp_src_i
);
    localparam int unsigned TotalNumRegisters  = (NumWarps * WarpWidth * 2**RegIdxWidth);
    localparam int unsigned RegistersPerBank   = TotalNumRegisters / NumBanks;
    localparam int unsigned BankRegAddrWidth   = $clog2(RegistersPerBank);
    localparam int unsigned NumOPCRequestPorts = NumOperandCollectors * OperandsPerInst;

    typedef logic [$clog2(NumOPCRequestPorts)-1:0] opc_tag_t;
    typedef logic [          $clog2(NumBanks)-1:0] bank_sel_t;
    typedef logic [          BankRegAddrWidth-1:0] bank_reg_addr_t;

    // #######################################################################################
    // # Signals                                                                            #
    // #######################################################################################

    /// Operand Collectors
    // Read Request
    logic           [NumOPCRequestPorts-1:0] opc_read_req_valid;
    logic           [NumOPCRequestPorts-1:0] opc_read_req_ready;
    bank_sel_t      [NumOPCRequestPorts-1:0] opc_read_req_bank_sel;
    bank_reg_addr_t [NumOPCRequestPorts-1:0] opc_read_req_addr;

    // Read Response
    logic  [NumOPCRequestPorts-1:0] opc_read_rsp_valid;
    data_t [NumOPCRequestPorts-1:0] opc_read_rsp_data;

    /// Register File Banks
    // Write port
    logic           [NumBanks-1:0] banks_write_req_valid;
    logic           [NumBanks-1:0] banks_write_req_ready;
    bank_reg_addr_t [NumBanks-1:0] banks_write_req_addr;
    data_t          [NumBanks-1:0] banks_write_req_data;

    // Read Request Interconnect to Register Banks Read Ports
    logic           [NumBanks-1:0] banks_read_req_valid;
    logic           [NumBanks-1:0] banks_read_req_ready;
    bank_reg_addr_t [NumBanks-1:0] banks_read_req_addr;
    opc_tag_t       [NumBanks-1:0] banks_read_req_tag;

    // Register Banks Read Response to Read Response Interconnect
    logic           [NumBanks-1:0] banks_read_rsp_valid;
    loigc           [NumBanks-1:0] banks_read_rsp_ready;
    opc_tag_t       [NumBanks-1:0] banks_read_rsp_tag;
    data_t          [NumBanks-1:0] banks_read_rsp_data;

    // #######################################################################################
    // # Read Request Interconnect between Operand Collectors and Register Banks             #
    // #######################################################################################

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

        // Request ports -> from Operand Collectors Read Request ports
        .data_i ( opc_read_req_addr     ),
        .sel_i  ( opc_read_req_bank_sel ),
        .valid_i( opc_read_req_valid    ),
        .ready_o( opc_read_req_ready    ),

        // Grant ports -> to Register Banks Read Ports
        .data_o ( banks_read_req_addr ),
        .idx_o  ( banks_read_req_tag  ),
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
        .payload_t  ( data_t             ),
        .OutSpillReg( 1'b0               ),
        .ExtPrio    ( 1'b0               ),
        .AxiVldRdy  ( 1'b0               ),
        .LockIn     ( 1'b0               ),
        .AxiVldMask ( '1                 )
    ) i_read_response_interconnect (
        .clk_i ( clk_i  ),
        .rst_ni( rst_ni ),

        // Request ports -> from Register Banks Read Ports
        .data_i ( banks_read_rsp_data  ),
        .sel_i  ( banks_read_rsp_tag   ),
        .valid_i( banks_read_rsp_valid ),
        .ready_o( banks_read_rsp_ready ),

        // Grant ports -> to Operand Collectors
        .data_o ( opc_read_rsp_data  ),
        .valid_o( opc_read_rsp_valid ),

        // Tie-Offs
        .flush_i( 1'b0         ),
        .rr_i   ( '0           ),
        .ready_i( '1           ),
        .idx_o  ( /* UNUSED */ ),
    );

    // ###################################################################################
    // # Register Banks                                                        #
    // ###################################################################################

    // Register Banks are each RegWidth wide -> store a register for a full warp
    for(int i = 0; i < NumBanks; i++) begin : gen_register_banks
        register_file_bank #(
            .DataWidth   ( RegWidth              ),
            .NumRegisters( RegistersPerBank      ),
            .DualPort    ( DualPortRegisterBanks )
        ) i_register_file_bank (
            .clk_i ( clk_i  ),
            .rst_ni( rst_ni ),

            // Write port
            .write_valid_i( banks_write_req_valid[i] ),
            .write_addr_i ( banks_write_req_addr [i] ),
            .write_data_i ( banks_write_req_data [i] ),
            .write_ready_o( banks_write_req_ready[i] ),

            // Read port
            .read_valid_i( banks_read_req_valid[i] ),
            .read_ready_o( banks_read_req_ready[i] ),
            .read_addr_i ( banks_read_req_addr [i] ),

            // Read output
            .read_valid_o( banks_read_rsp_valid[i] ),
            .read_addr_o ( banks_read_rsp_addr [i] ),
            .read_data_o ( banks_read_rsp_data [i] )
        );
    end : gen_register_banks
    // #######################################################################################
    // # Assertions                                                                          #
    // #######################################################################################

    // Check that the number of registers is divisible by the number of banks
    initial assert (TotalNumRegisters % NumBanks == 0) else
        $error("TotalNumRegisters % NumBanks != 0. This is not supported.");

    // Read Response Interconnect always has to be ready
    for(int i = 0; i < NumBanks; i++) begin : gen_read_response_interconnect_assertions
        assert property (@(posedge clk_i) disable iff (~rst_ni)
            (banks_read_valid_out[i] -> banks_read_ready_out[i])) else
            $error("Read Response Interconnect is not ready for bank %0d", i);
    end : gen_read_response_interconnect_assertions

endmodule : register_opc_stage
