// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

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

    // A single port BRAM is 32 bits wide
    localparam int unsigned SPWidth = 32;

    // How many address bits does a single port BRAM need?
    localparam int unsigned SPMaxAddrWidth = 14;
    localparam int unsigned BitsPerSP      = 1 << SPMaxAddrWidth;

    localparam logic [255:0] InitValue = (SimInit == "zeros") ? '0 : '1;

    typedef logic [SPWidth-1:0] bram_rdata_t; // Type for read data

    // Active high reset for BRAMs
    logic rst;
    assign rst = !rst_ni;

    if (NumPorts == 1) begin : gen_single_port
        // How many brams are needed for the given data width? -> width of bram array
        localparam int unsigned BramsForWidth = (DataWidth + SPWidth - 1) / SPWidth;

        `ifndef SYNTHESIS
            initial $display("BramsForWidth %0d, DataWidth %0d", BramsForWidth, DataWidth);
        `endif

        for (genvar x = 0; x < BramsForWidth; x++) begin : gen_bram_column
            // How Wide is the current bram column?
            localparam int unsigned ColumnWidth  = ((x == BramsForWidth - 1)
                                                    && ((DataWidth % SPWidth) != 0))
                                                    ? DataWidth % SPWidth : SPWidth;
            localparam int unsigned ByteInColumn = (ColumnWidth + 7) / 8;

            // How many words does a bram with ColumWidth have?
            localparam int unsigned WordsPerBram      = BitsPerSP / ColumnWidth;
            localparam int unsigned AddrWidthInColumn = $clog2(WordsPerBram);

            // How many BRAMs are needed in this column?
            localparam int unsigned BramsInColumn = (NumWords + WordsPerBram - 1) / WordsPerBram;

            localparam int unsigned BramSelBits = $clog2(BramsInColumn);

            `ifndef SYNTHESIS
                initial $display("Column %0d: W %0d, B %0d, WPB %0d, BIC %0d",
                    x, ColumnWidth, ByteInColumn, WordsPerBram, BramsInColumn);

                initial assert (BramsInColumn <= 8) else
                    $fatal(1, "BramsInColumn %0d exceeds 8 -> not implemented", BramsInColumn);
            `endif

            // Bram Selection, Address, Byte Enable and Data
            logic [2:0] bram_sel;
            logic [AddrWidthInColumn-1:0] bram_addr;
            logic [   SPMaxAddrWidth-1:0] bram_addr_be;
            logic [SPWidth-1:0] bram_data_in;

            // Upper bits of address is the BRAM select
            if (BramsInColumn == 1)
                assign bram_sel = '0; // Only one BRAM in this column, so select 0
            else if (BramsInColumn < 8) begin : gen_multirow_bram_sel
                always_comb begin
                    bram_sel = '0;
                    bram_sel[BramSelBits-1:0] = addr_i[0][AddrWidth-1-:BramSelBits];
                end
            end : gen_multirow_bram_sel
            else begin
                $error("BramsInColumn %0d exceeds 8 -> not implemented", BramsInColumn);
            end

            // Build address for the current BRAM
            always_comb begin : bram_addr_logic
                bram_addr = '0;
                if (BramsInColumn == 1) begin
                    /* verilator lint_off SELRANGE */
                    // Use full address as we do not select between different rows
                    bram_addr[AddrWidth-1:0] = addr_i[0][AddrWidth-1:0];
                    /* verilator lint_on SELRANGE */
                end else begin
                    // Use the lower bits of the address
                    bram_addr[AddrWidth-BramSelBits-1:0] = addr_i[0][AddrWidth-BramSelBits-1:0];
                end
            end : bram_addr_logic

            if (ByteInColumn == 1) // No byte enable
                always_comb begin
                    bram_addr_be = '0;
                    bram_addr_be[SPMaxAddrWidth-1-:AddrWidthInColumn] = bram_addr;
                end
            else begin : gen_multirow_bram_addr_be
                // Build Byte Enable
                // TODO: If ByteWidth != 8, this needs to be adapted!
                logic [     ByteInColumn-1:0] bram_be;
                assign bram_be = be_i[0][x * SPWidth / 8 +: ByteInColumn];

                always_comb begin
                    bram_addr_be = '0;
                    bram_addr_be[ByteInColumn-1:0] = bram_be;
                    bram_addr_be[SPMaxAddrWidth-1-:AddrWidthInColumn] = bram_addr;
                end
            end : gen_multirow_bram_addr_be

            // Write data -> Same for all BRAMs in this column
            if (ColumnWidth < SPWidth)
                assign bram_data_in[SPWidth-1:ColumnWidth] = '0; // Fill the upper bits with zero

            assign bram_data_in[ColumnWidth-1:0] = wdata_i[0][x * SPWidth +: ColumnWidth];

            // Read data output multiplexing
            bram_rdata_t [BramsInColumn-1:0] bram_data_out; // Data of each BRAM in this column

            if (BramsInColumn == 1) begin : gen_singlerow_rdata
                // If there is only one BRAM in this column, we can use the full address
                assign rdata_o[0][x * SPWidth +: ColumnWidth] = bram_data_out[0][ColumnWidth-1:0];
            end : gen_singlerow_rdata
            else begin : gen_multirow_rdata_mux
                logic [2:0] bram_sel_q; // Selected BRAM in this column for the read

                // Select the BRAM output
                assign rdata_o[0][x * SPWidth +: ColumnWidth] =
                                                        bram_data_out[bram_sel_q][ColumnWidth-1:0];

                always_ff @(posedge clk_i or negedge rst_ni) begin
                    if (!rst_ni) begin
                        bram_sel_q <= '0; // Reset the selected BRAM
                    end else if (req_i[0]) begin
                        bram_sel_q <= bram_sel; // Update the selected BRAM on read request
                    end
                end
            end : gen_multirow_rdata_mux

            // Generate BRAMs
            for (genvar y = 0; y < BramsInColumn; y++) begin : gen_bram
                // See Gowin UG285E for details
                SP #(
                    .READ_MODE  ( 2'b00       ),
                    .WRITE_MODE ( 2'b00       ),
                    .BIT_WIDTH  ( ColumnWidth ),
                    .BLK_SEL    ( y           ), // Select the current BRAM if BSEL == y
                    .RESET_MODE ( "ASYNC"     ),
                    .INIT_RAM_00( InitValue   ),
                    .INIT_RAM_01( InitValue   ),
                    .INIT_RAM_02( InitValue   ),
                    .INIT_RAM_03( InitValue   ),
                    .INIT_RAM_04( InitValue   ),
                    .INIT_RAM_05( InitValue   ),
                    .INIT_RAM_06( InitValue   ),
                    .INIT_RAM_07( InitValue   ),
                    .INIT_RAM_08( InitValue   ),
                    .INIT_RAM_09( InitValue   ),
                    .INIT_RAM_0A( InitValue   ),
                    .INIT_RAM_0B( InitValue   ),
                    .INIT_RAM_0C( InitValue   ),
                    .INIT_RAM_0D( InitValue   ),
                    .INIT_RAM_0E( InitValue   ),
                    .INIT_RAM_0F( InitValue   ),
                    .INIT_RAM_10( InitValue   ),
                    .INIT_RAM_11( InitValue   ),
                    .INIT_RAM_12( InitValue   ),
                    .INIT_RAM_13( InitValue   ),
                    .INIT_RAM_14( InitValue   ),
                    .INIT_RAM_15( InitValue   ),
                    .INIT_RAM_16( InitValue   ),
                    .INIT_RAM_17( InitValue   ),
                    .INIT_RAM_18( InitValue   ),
                    .INIT_RAM_19( InitValue   ),
                    .INIT_RAM_1A( InitValue   ),
                    .INIT_RAM_1B( InitValue   ),
                    .INIT_RAM_1C( InitValue   ),
                    .INIT_RAM_1D( InitValue   ),
                    .INIT_RAM_1E( InitValue   ),
                    .INIT_RAM_1F( InitValue   ),
                    .INIT_RAM_20( InitValue   ),
                    .INIT_RAM_21( InitValue   ),
                    .INIT_RAM_22( InitValue   ),
                    .INIT_RAM_23( InitValue   ),
                    .INIT_RAM_24( InitValue   ),
                    .INIT_RAM_25( InitValue   ),
                    .INIT_RAM_26( InitValue   ),
                    .INIT_RAM_27( InitValue   ),
                    .INIT_RAM_28( InitValue   ),
                    .INIT_RAM_29( InitValue   ),
                    .INIT_RAM_2A( InitValue   ),
                    .INIT_RAM_2B( InitValue   ),
                    .INIT_RAM_2C( InitValue   ),
                    .INIT_RAM_2D( InitValue   ),
                    .INIT_RAM_2E( InitValue   ),
                    .INIT_RAM_2F( InitValue   ),
                    .INIT_RAM_30( InitValue   ),
                    .INIT_RAM_31( InitValue   ),
                    .INIT_RAM_32( InitValue   ),
                    .INIT_RAM_33( InitValue   ),
                    .INIT_RAM_34( InitValue   ),
                    .INIT_RAM_35( InitValue   ),
                    .INIT_RAM_36( InitValue   ),
                    .INIT_RAM_37( InitValue   ),
                    .INIT_RAM_38( InitValue   ),
                    .INIT_RAM_39( InitValue   ),
                    .INIT_RAM_3A( InitValue   ),
                    .INIT_RAM_3B( InitValue   ),
                    .INIT_RAM_3C( InitValue   ),
                    .INIT_RAM_3D( InitValue   ),
                    .INIT_RAM_3E( InitValue   ),
                    .INIT_RAM_3F( InitValue   )
                ) i_bram (
                    .CLK    ( clk_i            ),
                    .RESET  ( rst              ),
                    .CE     ( req_i            ),
                    .WRE    ( we_i             ),
                    .OCE    ( 1'b1             ),
                    .BLKSEL ( bram_sel         ),
                    .AD     ( bram_addr_be     ),
                    .DI     ( bram_data_in     ),
                    .DO     ( bram_data_out[y] )
                );
            end : gen_bram
        end : gen_bram_column
    end : gen_single_port

// Validate parameters.
`ifndef SYNTHESIS
  initial begin: p_assertions
    assert (SimInit inside {"zeros", "ones"})
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
