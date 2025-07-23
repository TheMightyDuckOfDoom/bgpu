// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

(* blackbox *)
module tc_sram_blackbox (
    input logic clk_i,
    input logic rst_ni,

    input  logic req_i,
    input  logic we_i,
    input  logic [1023:0] addr_i,
    input  logic [1023:0] wdata_i,
    input  logic [1023:0] be_i,
    output logic [1023:0] rdata_o
);
endmodule : tc_sram_blackbox

module tc_sram #(
  parameter int unsigned NumWords     = 32'd1024, // Number of Words in data array
  parameter int unsigned DataWidth    = 32'd128,  // Data signal width (in bits)
  parameter int unsigned ByteWidth    = 32'd8,    // Width of a data byte (in bits)
  parameter int unsigned NumPorts     = 32'd2,    // Number of read and write ports
  parameter int unsigned Latency      = 32'd1,    // Latency when the read data is available
  parameter              SimInit      = "zeros",  // Simulation initialization, fixed to zero here!
  parameter bit          PrintSimCfg  = 1'b0,     // Print configuration
  parameter              ImplKey      = "none",   // Reference to specific implementation
  // DEPENDENT PARAMETERS, DO NOT OVERWRITE!
  parameter int unsigned AddrWidth = (NumWords > 32'd1) ? $clog2(NumWords) : 32'd1,
  parameter int unsigned BeWidth   = (DataWidth + ByteWidth - 32'd1) / ByteWidth, // ceil_div
  parameter type         addr_t    = logic [AddrWidth-1:0],
  parameter type         data_t    = logic [DataWidth-1:0],
  parameter type         be_t      = logic [BeWidth-1:0]
) (
  input  logic                clk_i,      // Clock
  input  logic                rst_ni,     // Asynchronous reset active low
  // input ports
  input  logic  [NumPorts-1:0] req_i,      // request
  input  logic  [NumPorts-1:0] we_i,       // write enable
  input  addr_t [NumPorts-1:0] addr_i,     // request address
  input  data_t [NumPorts-1:0] wdata_i,    // write data
  input  be_t   [NumPorts-1:0] be_i,       // write byte enable
  // output ports
  output data_t [NumPorts-1:0] rdata_o     // read data
);

    // RM_IHPSG13_1P_512x64_c2_bm_bist i_cut (
    //   .A_CLK   ( clk_i    ),
    //   .A_DLY   ( 1'b1     ),
    //   .A_ADDR  ( addr_i ),
    //   .A_BM    ( be_i     ),
    //   .A_MEN   ( req_i    ),
    //   .A_WEN   ( we_i     ),
    //   .A_REN   ( ~we_i    ),
    //   .A_DIN   ( wdata_i  ),
    //   .A_DOUT  ( rdata_o  )
    // );

    tc_sram_blackbox i_blackbox (
        .clk_i  ( clk_i      ),
        .rst_ni ( rst_ni     ),
        .req_i  ( req_i  [0] ),
        .we_i   ( we_i   [0] ),
        .addr_i ( addr_i [0] ),
        .wdata_i( wdata_i[0] ),
        .be_i   ( be_i   [0] ),
        .rdata_o( rdata_o[0] )
    );

// Validate parameters.
`ifndef SYNTHESIS
  initial begin: p_assertions
    assert ($bits(addr_i)  == NumPorts * AddrWidth)
        else $fatal(1, "AddrWidth problem on `addr_i`");
    assert ($bits(wdata_i) == NumPorts * DataWidth)
        else $fatal(1, "DataWidth problem on `wdata_i`");
    assert ($bits(be_i)    == NumPorts * BeWidth)
        else $fatal(1, "BeWidth   problem on `be_i`"   );
    assert ($bits(rdata_o) == NumPorts * DataWidth)
        else $fatal(1, "DataWidth problem on `rdata_o`");
    assert (NumWords  >= 32'd1) else $fatal(1, "NumWords has to be > 0");
    assert (DataWidth >= 32'd1) else $fatal(1, "DataWidth has to be > 0");
    assert (ByteWidth == 32'd8 || ByteWidth == 32'd1) else $fatal(1, "ByteWidth must be 1 or 8!");
    assert (NumPorts  == 32'd1) else $fatal(1, "The number of ports must be 1!");
    assert (Latency   == 32'd1) else $fatal(1, "The latency must be 1 cycle!");
  end
  initial begin: p_sim_hello
    if (PrintSimCfg) begin
      $display("#################################################################################");
      $display("tc_sram functional instantiated with the configuration:"                          );
      $display("Instance: %m"                                                                     );
      $display("Number of ports   (dec): %0d", NumPorts                                           );
      $display("Number of words   (dec): %0d", NumWords                                           );
      $display("Address width     (dec): %0d", AddrWidth                                          );
      $display("Data width        (dec): %0d", DataWidth                                          );
      $display("Byte width        (dec): %0d", ByteWidth                                          );
      $display("Byte enable width (dec): %0d", BeWidth                                            );
      $display("Latency Cycles    (dec): %0d", Latency                                            );
      $display("Simulation init   (str): %0s", SimInit                                            );
      $display("#################################################################################");
    end
  end
  for (genvar i = 0; i < NumPorts; i++) begin : gen_assertions
    assert property ( @(posedge clk_i) disable iff (!rst_ni)
        (req_i[i] |-> (addr_i[i] < NumWords))) else
      $warning("Request address %0h not mapped, port %0d, expect random write or read behavior!",
          addr_i[i], i);
  end

`endif

endmodule