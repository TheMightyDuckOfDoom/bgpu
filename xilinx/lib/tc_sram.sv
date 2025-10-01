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

    // A single port BRAM is upto 64 bits wide
    localparam int unsigned SPWidth = 64;

    // How many address bits does a single port BRAM need?
    localparam int unsigned SPMaxAddrWidth = 15;
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
            localparam int unsigned WordsPerBram      = BitsPerSP / SPWidth;
            localparam int unsigned AddrWidthInColumn = 16; //$clog2(WordsPerBram);

            // How many BRAMs are needed in this column?
            localparam int unsigned BramsInColumn = (NumWords + WordsPerBram - 1) / WordsPerBram;

            localparam int unsigned BramSelBits = BramsInColumn > 1 ? $clog2(BramsInColumn) : 1;

            `ifndef SYNTHESIS
                initial $display("Column %0d: W %0d, B %0d, WPB %0d, BIC %0d",
                    x, ColumnWidth, ByteInColumn, WordsPerBram, BramsInColumn);

                initial assert (BramsInColumn <= 8) else
                    $fatal(1, "BramsInColumn %0d exceeds 8 -> not implemented", BramsInColumn);
            `endif

            // Bram Selection, Address, Byte Enable and Data
            logic [BramSelBits-1:0] bram_sel;
            logic [AddrWidthInColumn-1:0] bram_addr;
            logic [7:0] bram_be;
            logic [SPWidth-1:0] bram_data_in;

            // Upper bits of address is the BRAM select
            if (BramsInColumn == 1)
                assign bram_sel = '0; // Only one BRAM in this column, so select 0
            else begin : gen_multirow_bram_sel
                always_comb begin
                    bram_sel = '0;
                    bram_sel[BramSelBits-1:0] = addr_i[0][AddrWidth-1-:BramSelBits];
                end
            end : gen_multirow_bram_sel

            // Build address for the current BRAM
            always_comb begin : bram_addr_logic
                bram_addr = '0;
                bram_addr[AddrWidth+5:6] = addr_i[0][AddrWidth-1:0];
            end : bram_addr_logic

            // Byte enable
            always_comb begin : bram_be_logic
                bram_be = '0;
                if (we_i[0]) begin
                    // If we are writing, use the byte enable from the request
                    bram_be[ByteInColumn-1:0] = be_i[0][x * ByteInColumn +: ByteInColumn];
                end
            end : bram_be_logic

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
                logic [BramSelBits-1:0] bram_sel_q; // Selected BRAM in this column for the read

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
                // See AMD UG473 for details
                // Needed to add DONT_TOUCH as phys_opt_design somehow broke the design without it
                (* DONT_TOUCH = "yes" *) RAMB36E1 #(
                    .DOA_REG          ( 0             ),
                    .DOB_REG          ( 0             ),
                    .EN_ECC_READ      ( "FALSE"       ),
                    .EN_ECC_WRITE     ( "FALSE"       ),
                    .INIT_A           ( '0            ),
                    .INIT_B           ( '0            ),
                    .INIT_FILE        ( "NONE"        ),
                    .RAM_EXTENSION_A  ( "NONE"        ),
                    .RAM_EXTENSION_B  ( "NONE"        ),
                    .RAM_MODE         ( "SDP"         ),
                    .READ_WIDTH_A     ( 72            ),
                    .READ_WIDTH_B     ( 0             ),
                    .WRITE_WIDTH_A    ( 0             ),
                    .WRITE_WIDTH_B    ( 72            ),
                    .RSTREG_PRIORITY_A( "RSTREG"      ),
                    .RSTREG_PRIORITY_B( "RSTREG"      ),
                    .SIM_DEVICE       ( "7SERIES"     ),
                    .SRVAL_A          ( '0            ),
                    .SRVAL_B          ( '0            ),
                    .WRITE_MODE_A     ( "WRITE_FIRST" ),
                    .WRITE_MODE_B     ( "WRITE_FIRST" ),
                    .INIT_00          ( InitValue     ),
                    .INIT_01          ( InitValue     ),
                    .INIT_02          ( InitValue     ),
                    .INIT_03          ( InitValue     ),
                    .INIT_04          ( InitValue     ),
                    .INIT_05          ( InitValue     ),
                    .INIT_06          ( InitValue     ),
                    .INIT_07          ( InitValue     ),
                    .INIT_08          ( InitValue     ),
                    .INIT_09          ( InitValue     ),
                    .INIT_0A          ( InitValue     ),
                    .INIT_0B          ( InitValue     ),
                    .INIT_0C          ( InitValue     ),
                    .INIT_0D          ( InitValue     ),
                    .INIT_0E          ( InitValue     ),
                    .INIT_0F          ( InitValue     ),
                    .INIT_10          ( InitValue     ),
                    .INIT_11          ( InitValue     ),
                    .INIT_12          ( InitValue     ),
                    .INIT_13          ( InitValue     ),
                    .INIT_14          ( InitValue     ),
                    .INIT_15          ( InitValue     ),
                    .INIT_16          ( InitValue     ),
                    .INIT_17          ( InitValue     ),
                    .INIT_18          ( InitValue     ),
                    .INIT_19          ( InitValue     ),
                    .INIT_1A          ( InitValue     ),
                    .INIT_1B          ( InitValue     ),
                    .INIT_1C          ( InitValue     ),
                    .INIT_1D          ( InitValue     ),
                    .INIT_1E          ( InitValue     ),
                    .INIT_1F          ( InitValue     ),
                    .INIT_20          ( InitValue     ),
                    .INIT_21          ( InitValue     ),
                    .INIT_22          ( InitValue     ),
                    .INIT_23          ( InitValue     ),
                    .INIT_24          ( InitValue     ),
                    .INIT_25          ( InitValue     ),
                    .INIT_26          ( InitValue     ),
                    .INIT_27          ( InitValue     ),
                    .INIT_28          ( InitValue     ),
                    .INIT_29          ( InitValue     ),
                    .INIT_2A          ( InitValue     ),
                    .INIT_2B          ( InitValue     ),
                    .INIT_2C          ( InitValue     ),
                    .INIT_2D          ( InitValue     ),
                    .INIT_2E          ( InitValue     ),
                    .INIT_2F          ( InitValue     ),
                    .INIT_30          ( InitValue     ),
                    .INIT_31          ( InitValue     ),
                    .INIT_32          ( InitValue     ),
                    .INIT_33          ( InitValue     ),
                    .INIT_34          ( InitValue     ),
                    .INIT_35          ( InitValue     ),
                    .INIT_36          ( InitValue     ),
                    .INIT_37          ( InitValue     ),
                    .INIT_38          ( InitValue     ),
                    .INIT_39          ( InitValue     ),
                    .INIT_3A          ( InitValue     ),
                    .INIT_3B          ( InitValue     ),
                    .INIT_3C          ( InitValue     ),
                    .INIT_3D          ( InitValue     ),
                    .INIT_3E          ( InitValue     ),
                    .INIT_3F          ( InitValue     ),
                    .INIT_40          ( InitValue     ),
                    .INIT_41          ( InitValue     ),
                    .INIT_42          ( InitValue     ),
                    .INIT_43          ( InitValue     ),
                    .INIT_44          ( InitValue     ),
                    .INIT_45          ( InitValue     ),
                    .INIT_46          ( InitValue     ),
                    .INIT_47          ( InitValue     ),
                    .INIT_48          ( InitValue     ),
                    .INIT_49          ( InitValue     ),
                    .INIT_4A          ( InitValue     ),
                    .INIT_4B          ( InitValue     ),
                    .INIT_4C          ( InitValue     ),
                    .INIT_4D          ( InitValue     ),
                    .INIT_4E          ( InitValue     ),
                    .INIT_4F          ( InitValue     ),
                    .INIT_50          ( InitValue     ),
                    .INIT_51          ( InitValue     ),
                    .INIT_52          ( InitValue     ),
                    .INIT_53          ( InitValue     ),
                    .INIT_54          ( InitValue     ),
                    .INIT_55          ( InitValue     ),
                    .INIT_56          ( InitValue     ),
                    .INIT_57          ( InitValue     ),
                    .INIT_58          ( InitValue     ),
                    .INIT_59          ( InitValue     ),
                    .INIT_5A          ( InitValue     ),
                    .INIT_5B          ( InitValue     ),
                    .INIT_5C          ( InitValue     ),
                    .INIT_5D          ( InitValue     ),
                    .INIT_5E          ( InitValue     ),
                    .INIT_5F          ( InitValue     ),
                    .INIT_60          ( InitValue     ),
                    .INIT_61          ( InitValue     ),
                    .INIT_62          ( InitValue     ),
                    .INIT_63          ( InitValue     ),
                    .INIT_64          ( InitValue     ),
                    .INIT_65          ( InitValue     ),
                    .INIT_66          ( InitValue     ),
                    .INIT_67          ( InitValue     ),
                    .INIT_68          ( InitValue     ),
                    .INIT_69          ( InitValue     ),
                    .INIT_6A          ( InitValue     ),
                    .INIT_6B          ( InitValue     ),
                    .INIT_6C          ( InitValue     ),
                    .INIT_6D          ( InitValue     ),
                    .INIT_6E          ( InitValue     ),
                    .INIT_6F          ( InitValue     ),
                    .INIT_70          ( InitValue     ),
                    .INIT_71          ( InitValue     ),
                    .INIT_72          ( InitValue     ),
                    .INIT_73          ( InitValue     ),
                    .INIT_74          ( InitValue     ),
                    .INIT_75          ( InitValue     ),
                    .INIT_76          ( InitValue     ),
                    .INIT_77          ( InitValue     ),
                    .INIT_78          ( InitValue     ),
                    .INIT_79          ( InitValue     ),
                    .INIT_7A          ( InitValue     ),
                    .INIT_7B          ( InitValue     ),
                    .INIT_7C          ( InitValue     ),
                    .INIT_7D          ( InitValue     ),
                    .INIT_7E          ( InitValue     ),
                    .INIT_7F          ( InitValue     ),
                    .INITP_00         ( InitValue     ),
                    .INITP_01         ( InitValue     ),
                    .INITP_02         ( InitValue     ),
                    .INITP_03         ( InitValue     ),
                    .INITP_04         ( InitValue     ),
                    .INITP_05         ( InitValue     ),
                    .INITP_06         ( InitValue     ),
                    .INITP_07         ( InitValue     ),
                    .INITP_08         ( InitValue     ),
                    .INITP_09         ( InitValue     ),
                    .INITP_0A         ( InitValue     ),
                    .INITP_0B         ( InitValue     ),
                    .INITP_0C         ( InitValue     ),
                    .INITP_0D         ( InitValue     ),
                    .INITP_0E         ( InitValue     ),
                    .INITP_0F         ( InitValue     )
                ) i_bram (
                    .CLKARDCLK    ( clk_i ),
                    .CLKBWRCLK    ( clk_i ),
                    .RSTRAMARSTRAM( rst   ),
                    .RSTRAMB      ( rst   ),
                    .RSTREGARSTREG( rst   ),
                    .RSTREGB      ( rst   ),

                    .ADDRARDADDR  ( bram_addr               ),
                    .ADDRBWRADDR  ( bram_addr               ),
                    .DIADI        ( bram_data_in[31:0]      ),
                    .DIBDI        ( bram_data_in[63:32]     ),
                    .DOADO        ( bram_data_out[y][31:0]  ),
                    .DOBDO        ( bram_data_out[y][63:32] ),
                    .ENARDEN      ( req_i[0] & !we_i[0]     ),
                    .ENBWREN      ( req_i[0] &  we_i[0]     ),
                    .WEBWE        ( bram_be                 ),
                    // Tie-offs
                    .INJECTDBITERR( 1'b0 ),
                    .INJECTSBITERR( 1'b0 ),
                    .REGCEAREGCE  ( 1'b1 ),
                    .REGCEB       ( 1'b1 ),
                    .CASCADEINA   ( 1'b0 ),
                    .CASCADEINB   ( 1'b0 ),
                    .DIPADIP      ( '0   ),
                    .DIPBDIP      ( '0   ),
                    .WEA          ( '0   ),
                    // Unconnected
                    .RDADDRECC   ( /* NOT CONNECTED */ ),
                    .SBITERR     ( /* NOT CONNECTED */ ),
                    .DBITERR     ( /* NOT CONNECTED */ ),
                    .CASCADEOUTA ( /* NOT CONNECTED */ ),
                    .CASCADEOUTB ( /* NOT CONNECTED */ ),
                    .DOPADOP     ( /* NOT CONNECTED */ ),
                    .DOPBDOP     ( /* NOT CONNECTED */ ),
                    .ECCPARITY   ( /* NOT CONNECTED */ )
                );
            end : gen_bram
        end : gen_bram_column
    end : gen_single_port

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
