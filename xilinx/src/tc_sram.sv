// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// CAUTION: I'm not confident that this works correctly, but it seems to work
module tc_sram #(
  parameter int unsigned NumWords     = 32'd1024, // Number of Words in data array
  parameter int unsigned DataWidth    = 32'd128,  // Data signal width (in bits)
  parameter int unsigned ByteWidth    = 32'd8,    // Width of a data byte (in bits)
  parameter int unsigned NumPorts     = 32'd2,    // Number of read and write ports
  parameter int unsigned Latency      = 32'd1,    // Latency when the read data is available
  parameter string       SimInit      = "zeros",  // Simulation initialization, fixed to zero here!
  parameter bit          PrintSimCfg  = 1'b0,     // Print configuration
  parameter string       ImplKey      = "none",   // Reference to specific implementation
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

    data_t mem_q [2**AddrWidth - 1 : 0];

    always_ff @(posedge clk_i) begin
        if (req_i[0] && we_i[0])
            for (int b = 0; b < BeWidth; b++)
                if (be_i[0][b])
                    mem_q[addr_i[0]][b*ByteWidth +: ByteWidth] <= wdata_i[0][b*ByteWidth +: ByteWidth];
    end

    always @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni)
            rdata_o[0] <= '0;
        else if (req_i[0] && !we_i[0])
            rdata_o[0] <= mem_q[addr_i[0]];
    end

// Validate parameters.
`ifndef SYNTHESIS
    initial begin: p_assertions
        assert ((SimInit == "zeros") || (SimInit == "ones"))
            else $fatal(1, "The Gowin `tc_sram` has fixed SimInit: 'zeros' or 'ones'");
        assert ($bits(addr_i)  == NumPorts * AddrWidth)
            else $fatal(1, "AddrWidth problem on `addr_i`");
        assert ($bits(wdata_i) == NumPorts * DataWidth)
            else $fatal(1, "DataWidth problem on `wdata_i`");
        assert ($bits(be_i)    == NumPorts * BeWidth)
            else $fatal(1, "BeWidth   problem on `be_i`"   );
        assert ($bits(rdata_o) == NumPorts * DataWidth)
            else $fatal(1, "DataWidth problem on `rdata_o`");
        assert (NumWords  >= 32'd1) else $fatal(1, "NumWords has to be > 0");
        assert (NumWords == (1 << $clog2(NumWords))) else $fatal(1, "NumWords has to be a power of 2");
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
            (req_i[i] |-> (32'(addr_i[i]) < NumWords))) else
        $warning("Request address %0h not mapped, port %0d, expect random write or read behavior!",
            addr_i[i], i, NumWords);
    end

`endif

endmodule
