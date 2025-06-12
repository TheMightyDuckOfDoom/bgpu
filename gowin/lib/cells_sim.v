/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

(* abc9_lut=1 *)
module LUT1(output F, input I0);
	parameter [1:0] INIT = 0;
	specify
		(I0 => F) = (555, 902);
	endspecify
	assign F = I0 ? INIT[1] : INIT[0];
endmodule

(* abc9_lut=1 *)
module LUT2(output F, input I0, I1);
	parameter [3:0] INIT = 0;
	specify
		(I0 => F) = (867, 1184);
		(I1 => F) = (555, 902);
	endspecify
	wire [ 1: 0] s1 = I1 ? INIT[ 3: 2] : INIT[ 1: 0];
	assign F = I0 ? s1[1] : s1[0];
endmodule

(* abc9_lut=1 *)
module LUT3(output F, input I0, I1, I2);
	parameter [7:0] INIT = 0;
	specify
		(I0 => F) = (1054, 1486);
		(I1 => F) = (867, 1184);
		(I2 => F) = (555, 902);
	endspecify	
	wire [ 3: 0] s2 = I2 ? INIT[ 7: 4] : INIT[ 3: 0];
	wire [ 1: 0] s1 = I1 ?   s2[ 3: 2] :   s2[ 1: 0];
	assign F = I0 ? s1[1] : s1[0];
endmodule

(* abc9_lut=1 *)
module LUT4(output F, input I0, I1, I2, I3);
	parameter [15:0] INIT = 0;
	specify
		(I0 => F) = (1054, 1486);
		(I1 => F) = (1053, 1583);
		(I2 => F) = (867, 1184);
		(I3 => F) = (555, 902);
	endspecify	
	wire [ 7: 0] s3 = I3 ? INIT[15: 8] : INIT[ 7: 0];
	wire [ 3: 0] s2 = I2 ?   s3[ 7: 4] :   s3[ 3: 0];
	wire [ 1: 0] s1 = I1 ?   s2[ 3: 2] :   s2[ 1: 0];
	assign F = I0 ? s1[1] : s1[0];
endmodule

(* abc9_lut=2 *)
module __APICULA_LUT5(output F, input I0, I1, I2, I3, M0);
	specify
		(I0 => F) = (1187, 1638);
		(I1 => F) = (1184, 1638);
		(I2 => F) = (995, 1371);
		(I3 => F) = (808, 1116);
		(M0 => F) = (486, 680);
	endspecify	
endmodule

(* abc9_lut=4 *)
module __APICULA_LUT6(output F, input I0, I1, I2, I3, M0, M1);
	specify
		(I0 => F) = (1187 + 136, 1638 + 255);
		(I1 => F) = (1184 + 136, 1638 + 255);
		(I2 => F) = (995 + 136, 1371 + 255);
		(I3 => F) = (808 + 136, 1116 + 255);
		(M0 => F) = (486 + 136, 680 + 255);
		(M1 => F) = (478, 723);
	endspecify	
endmodule

(* abc9_lut=8 *)
module __APICULA_LUT7(output F, input I0, I1, I2, I3, M0, M1, M2);
	specify
		(I0 => F) = (1187 + 136 + 136, 1638 + 255 + 255);
		(I1 => F) = (1184 + 136 + 136, 1638 + 255 + 255);
		(I2 => F) = (995 + 136 + 136, 1371 + 255 + 255);
		(I3 => F) = (808 + 136 + 136, 1116 + 255 + 255);
		(M0 => F) = (486 + 136 + 136, 680 + 255 + 255);
		(M1 => F) = (478 + 136, 723 + 255);
		(M2 => F) = (478, 723);
	endspecify	
endmodule

(* abc9_lut=16 *)
module __APICULA_LUT8(output F, input I0, I1, I2, I3, M0, M1, M2, M3);
		specify
		(I0 => F) = (1187 + 136 + 136 + 136, 1638 + 255 + 255 + 255);
		(I1 => F) = (1184 + 136 + 136 + 136, 1638 + 255 + 255 + 255);
		(I2 => F) = (995 + 136 + 136 + 136, 1371 + 255 + 255 + 255);
		(I3 => F) = (808 + 136 + 136 + 136, 1116 + 255 + 255 + 255);
		(M0 => F) = (486 + 136 + 136 + 136, 680 + 255 + 255 + 255);
		(M1 => F) = (478 + 136 + 136, 723 + 255 + 255);
		(M2 => F) = (478 + 136, 723 + 255);
		(M3 => F) = (478, 723);
		endspecify	
	endmodule

module MUX2 (O, I0, I1, S0);
  input I0,I1;
  input S0;
  output O;

	specify
		(I0 => O) = (141, 160);
		(I1 => O) = (141, 160);
		(S0 => O) = (486, 680);
	endspecify

  assign O = S0 ? I1 : I0;
endmodule

module MUX2_LUT5 (O, I0, I1, S0);
  input I0,I1;
  input S0;
  output O;

	specify
		(I0 => O) = (141, 160);
		(I1 => O) = (141, 160);
		(S0 => O) = (486, 680);
	endspecify

  MUX2 mux2_lut5 (O, I0, I1, S0);
endmodule

module MUX2_LUT6 (O, I0, I1, S0);
  input I0,I1;
  input S0;
  output O;

	specify
		(I0 => O) = (136, 255);
		(I1 => O) = (136, 255);
		(S0 => O) = (478, 723);
	endspecify

  MUX2 mux2_lut6 (O, I0, I1, S0);
endmodule

module MUX2_LUT7 (O, I0, I1, S0);
  input I0,I1;
  input S0;
  output O;

	specify
		(I0 => O) = (136, 255);
		(I1 => O) = (136, 255);
		(S0 => O) = (478, 723);
	endspecify

  MUX2 mux2_lut7 (O, I0, I1, S0);
endmodule

module MUX2_LUT8 (O, I0, I1, S0);
  input I0,I1;
  input S0;
  output O;

	specify
		(I0 => O) = (136, 255);
		(I1 => O) = (136, 255);
		(S0 => O) = (478, 723);
	endspecify

  MUX2 mux2_lut8 (O, I0, I1, S0);
endmodule

(* abc9_flop, lib_whitebox *)
module DFF (output reg Q, input CLK, D);
	parameter [0:0] INIT = 1'b0;
	initial Q = INIT;

	specify
		(posedge CLK => (Q : D)) = (480, 660);
		$setup(D, posedge CLK, 576);
	endspecify

	always @(posedge CLK)
		Q <= D;
endmodule

(* abc9_flop, lib_whitebox *)
module DFFE (output reg Q, input D, CLK, CE);
  parameter [0:0] INIT = 1'b0;
  initial Q = INIT;

	specify
		if (CE) (posedge CLK => (Q : D)) = (480, 660);
		$setup(D, posedge CLK &&& CE, 576);
		$setup(CE, posedge CLK, 63);
	endspecify

  always @(posedge CLK) begin
    if (CE)
      Q <= D;
  end
endmodule // DFFE (positive clock edge; clock enable)

(* abc9_flop, lib_whitebox *)
module DFFS (output reg Q, input D, CLK, SET);
  parameter [0:0] INIT = 1'b1;
  initial Q = INIT;

	specify
		(posedge CLK => (Q : D)) = (480, 660);
		$setup(D, posedge CLK, 576);
		$setup(SET, posedge CLK, 63);
	endspecify

  always @(posedge CLK) begin
    if (SET)
      Q <= 1'b1;
    else
      Q <= D;	
  end
endmodule // DFFS (positive clock edge; synchronous set)

(* abc9_flop, lib_whitebox *)
module DFFSE (output reg Q, input D, CLK, CE, SET);
  parameter [0:0] INIT = 1'b1;
  initial Q = INIT;

	specify
		if (CE) (posedge CLK => (Q : D)) = (480, 660);
		$setup(D, posedge CLK &&& CE, 576);
		$setup(CE, posedge CLK, 63);
		$setup(SET, posedge CLK, 63);
	endspecify

  always @(posedge CLK) begin
    if (SET)
      Q <= 1'b1;
    else if (CE)
      Q <= D;
end
endmodule // DFFSE (positive clock edge; synchronous set takes precedence over clock enable)

(* abc9_flop, lib_whitebox *)
module DFFR (output reg Q, input D, CLK, RESET);
  parameter [0:0] INIT = 1'b0;
  initial Q = INIT;

	specify
		(posedge CLK => (Q : D)) = (480, 660);
		$setup(D, posedge CLK, 576);
		$setup(RESET, posedge CLK, 63);
	endspecify

  always @(posedge CLK) begin
    if (RESET)
      Q <= 1'b0;
    else
      Q <= D;
  end
endmodule // DFFR (positive clock edge; synchronous reset)

(* abc9_flop, lib_whitebox *)
module DFFRE (output reg Q, input D, CLK, CE, RESET);
  parameter [0:0] INIT = 1'b0;
  initial Q = INIT;

	specify
		if (CE) (posedge CLK => (Q : D)) = (480, 660);
		$setup(D, posedge CLK &&& CE, 576);
		$setup(CE, posedge CLK, 63);
		$setup(RESET, posedge CLK, 63);
	endspecify

  always @(posedge CLK) begin
    if (RESET)
      Q <= 1'b0;
    else if (CE)
      Q <= D;
  end
endmodule // DFFRE (positive clock edge; synchronous reset takes precedence over clock enable)

(* abc9_box, lib_whitebox *)
module DFFP (output reg Q, input D, CLK, PRESET);
  parameter [0:0] INIT = 1'b1;
  initial Q = INIT;

	specify
		(posedge CLK => (Q : D)) = (480, 660);
		(PRESET => Q) = (1800, 2679);
		$setup(D, posedge CLK, 576);
	endspecify

  always @(posedge CLK or posedge PRESET) begin
    if(PRESET)
      Q <= 1'b1;
    else
      Q <= D;
  end
endmodule // DFFP (positive clock edge; asynchronous preset)

(* abc9_box, lib_whitebox *)
module DFFPE (output reg Q, input D, CLK, CE, PRESET);
  parameter [0:0] INIT = 1'b1;
  initial Q = INIT;

	specify
		if (CE) (posedge CLK => (Q : D)) = (480, 660);
		(PRESET => Q) = (1800, 2679);
		$setup(D, posedge CLK &&& CE, 576);
		$setup(CE, posedge CLK, 63);
	endspecify

  always @(posedge CLK or posedge PRESET) begin
    if(PRESET)
      Q <= 1'b1;
    else if (CE)
      Q <= D;
  end
endmodule // DFFPE (positive clock edge; asynchronous preset; clock enable)

(* abc9_box, lib_whitebox *)
module DFFC (output reg Q, input D, CLK, CLEAR);
  parameter [0:0] INIT = 1'b0;
  initial Q = INIT;

	specify
		(posedge CLK => (Q : D)) = (480, 660);
		(CLEAR => Q) = (1800, 2679);
		$setup(D, posedge CLK, 576);
	endspecify

  always @(posedge CLK or posedge CLEAR) begin
    if(CLEAR)
      Q <= 1'b0;
    else
      Q <= D;
  end
endmodule // DFFC (positive clock edge; asynchronous clear)

(* abc9_box, lib_whitebox *)
module DFFCE (output reg Q, input D, CLK, CE, CLEAR);
  parameter [0:0] INIT = 1'b0;
  initial Q = INIT;

	specify
		if (CE) (posedge CLK => (Q : D)) = (480, 660);
		(CLEAR => Q) = (1800, 2679);
		$setup(D, posedge CLK &&& CE, 576);
		$setup(CE, posedge CLK, 63);
	endspecify

  always @(posedge CLK or posedge CLEAR) begin
    if(CLEAR)
      Q <= 1'b0;
    else if (CE)
      Q <= D;
  end
endmodule // DFFCE (positive clock edge; asynchronous clear; clock enable)

(* abc9_flop, lib_whitebox *)
module DFFN (output reg Q, input CLK, D);
	parameter [0:0] INIT = 1'b0;
	initial Q = INIT;

  specify
    (negedge CLK => (Q : D)) = (480, 660);
    $setup(D, negedge CLK, 576);
  endspecify

	always @(negedge CLK)
		Q <= D;
endmodule

(* abc9_flop, lib_whitebox *)
module DFFNE (output reg Q, input D, CLK, CE);
  parameter [0:0] INIT = 1'b0;
  initial Q = INIT;

	specify
		if (CE) (negedge CLK => (Q : D)) = (480, 660);
		$setup(D, negedge CLK &&& CE, 576);
		$setup(CE, negedge CLK, 63);
	endspecify

  always @(negedge CLK) begin
    if (CE)
      Q <= D;
  end
endmodule // DFFNE (negative clock edge; clock enable)

(* abc9_flop, lib_whitebox *)
module DFFNS (output reg Q, input D, CLK, SET);
  parameter [0:0] INIT = 1'b1;
  initial Q = INIT;
  
	specify
		(negedge CLK => (Q : D)) = (480, 660);
		$setup(D, negedge CLK, 576);
		$setup(SET, negedge CLK, 63);
	endspecify

  always @(negedge CLK) begin
    if (SET)
      Q <= 1'b1;
    else
      Q <= D;	
  end
endmodule // DFFNS (negative clock edge; synchronous set)

(* abc9_flop, lib_whitebox *)
module DFFNSE (output reg Q, input D, CLK, CE, SET);
  parameter [0:0] INIT = 1'b1;
  initial Q = INIT;

	specify
		if (CE) (negedge CLK => (Q : D)) = (480, 660);
		$setup(D, negedge CLK &&& CE, 576);
		$setup(CE, negedge CLK, 63);
		$setup(SET, negedge CLK, 63);
	endspecify

  always @(negedge CLK) begin
    if (SET)
      Q <= 1'b1;
    else if (CE)
      Q <= D;
end
endmodule // DFFNSE (negative clock edge; synchronous set takes precedence over clock enable)

(* abc9_flop, lib_whitebox *)
module DFFNR (output reg Q, input D, CLK, RESET);
  parameter [0:0] INIT = 1'b0;
  initial Q = INIT;

	specify
		(negedge CLK => (Q : D)) = (480, 660);
		$setup(D, negedge CLK, 576);
		$setup(RESET, negedge CLK, 63);
	endspecify

  always @(negedge CLK) begin
    if (RESET)
      Q <= 1'b0;
    else
      Q <= D;
  end
endmodule // DFFNR (negative clock edge; synchronous reset)

(* abc9_flop, lib_whitebox *)
module DFFNRE (output reg Q, input D, CLK, CE, RESET);
  parameter [0:0] INIT = 1'b0;
  initial Q = INIT;

	specify
		if (CE) (negedge CLK => (Q : D)) = (480, 660);
		$setup(D, negedge CLK &&& CE, 576);
		$setup(CE, negedge CLK, 63);
		$setup(RESET, negedge CLK, 63);
	endspecify

  always @(negedge CLK) begin
    if (RESET)
      Q <= 1'b0;
    else if (CE)
      Q <= D;
  end
endmodule // DFFNRE (negative clock edge; synchronous reset takes precedence over clock enable)

(* abc9_box, lib_whitebox *)
module DFFNP (output reg Q, input D, CLK, PRESET);
  parameter [0:0] INIT = 1'b1;
  initial Q = INIT;

	specify
		(negedge CLK => (Q : D)) = (480, 660);
		(PRESET => Q) = (1800, 2679);
		$setup(D, negedge CLK, 576);
	endspecify

  always @(negedge CLK or posedge PRESET) begin
    if(PRESET)
      Q <= 1'b1;
    else
      Q <= D;
  end
endmodule // DFFNP (negative clock edge; asynchronous preset)

(* abc9_box, lib_whitebox *)
module DFFNPE (output reg Q, input D, CLK, CE, PRESET);
  parameter [0:0] INIT = 1'b1;
  initial Q = INIT;
  
	specify
		if (CE) (negedge CLK => (Q : D)) = (480, 660);
		(PRESET => Q) = (1800, 2679);
		$setup(D, negedge CLK &&& CE, 576);
		$setup(CE, negedge CLK, 63);
	endspecify

  always @(negedge CLK or posedge PRESET) begin
    if(PRESET)
      Q <= 1'b1;
    else if (CE)
      Q <= D;
  end
endmodule // DFFNPE (negative clock edge; asynchronous preset; clock enable)

(* abc9_box, lib_whitebox *)
module DFFNC (output reg Q, input D, CLK, CLEAR);
  parameter [0:0] INIT = 1'b0;
  initial Q = INIT;

	specify
		(negedge CLK => (Q : D)) = (480, 660);
		(CLEAR => Q) = (1800, 2679);
		$setup(D, negedge CLK, 576);
	endspecify

  always @(negedge CLK or posedge CLEAR) begin
    if(CLEAR)
      Q <= 1'b0;
    else
      Q <= D;
  end
endmodule // DFFNC (negative clock edge; asynchronous clear)

(* abc9_box, lib_whitebox *)
module DFFNCE (output reg Q, input D, CLK, CE, CLEAR);
  parameter [0:0] INIT = 1'b0;
  initial Q = INIT;

	specify
		if (CE) (negedge CLK => (Q : D)) = (480, 660);
		(CLEAR => Q) = (1800, 2679);
		$setup(D, negedge CLK &&& CE, 576);
		$setup(CE, negedge CLK, 63);
	endspecify

  always @(negedge CLK or posedge CLEAR) begin
    if(CLEAR)
      Q <= 1'b0;
    else if (CE)
      Q <= D;
  end
endmodule // DFFNCE (negative clock edge; asynchronous clear; clock enable)

// TODO add more DFF sim cells

module VCC(output V);
	assign V = 1;
endmodule

module GND(output G);
	assign G = 0;
endmodule

module IBUF(output O, input I);

	specify
		(I => O) = 0;
	endspecify

	assign O = I;
endmodule

module OBUF(output O, input I);

	specify
		(I => O) = 0;
	endspecify

	assign O = I;
endmodule

module TBUF (O, I, OEN);
  input I, OEN;
  output O;
  assign O = OEN ? 1'bz : I;
endmodule

module IOBUF (O, IO, I, OEN);
  input I,OEN;
  output O;
  inout IO;
  assign IO = OEN ? 1'bz : I;
  assign I = IO;
endmodule

module ELVDS_OBUF (I, O, OB);
  input I;
  output O;
  output OB;
  assign O = I;
  assign OB = ~I;
endmodule

module TLVDS_OBUF (I, O, OB);
  input I;
  output O;
  output OB;
  assign O = I;
  assign OB = ~I;
endmodule

module OSER4(D3, D2, D1, D0, TX1, TX0, FCLK, PCLK, RESET, Q1, Q0);
	output Q1;
	output Q0;

	input D3;
	input D2;
	input D1;
	input D0;
	input TX1;
	input TX0;
	input FCLK;
	input PCLK;
	input RESET;

	parameter GSREN = "false";
	parameter LSREN = "true";
	parameter TXCLK_POL = 0;
	parameter HWL = "false";
endmodule

module OSER4_MEM (Q0, Q1, D0, D1, D2, D3, TX0, TX1, PCLK, FCLK, TCLK, RESET)  ;
    parameter GSREN = "";
    parameter LSREN = "";
    parameter HWL = "";
    parameter TCLK_SOURCE = "";
    parameter TXCLK_POL = "";

    input D0, D1, D2, D3;
    input TX0, TX1;
    input PCLK, FCLK, TCLK, RESET;
    output  Q0,  Q1;

    parameter ID = "";
endmodule

module OSER8(D7, D6, D5, D4, D3, D2, D1, D0, TX3, TX2, TX1, TX0, FCLK, PCLK, RESET, Q1, Q0);
	output Q1;
	output Q0;

	input D7;
	input D6;
	input D5;
	input D4;
	input D3;
	input D2;
	input D1;
	input D0;
	input TX3;
	input TX2;
	input TX1;
	input TX0;
	input FCLK;
	input PCLK;
	input RESET;

	parameter GSREN = "false";
	parameter LSREN = "true";
	parameter TXCLK_POL = 0;
	parameter HWL = "false";
endmodule

module OSER10(D9, D8, D7, D6, D5, D4, D3, D2, D1, D0, FCLK, PCLK, RESET, Q);
	output Q;

	input D9;
	input D8;
	input D7;
	input D6;
	input D5;
	input D4;
	input D3;
	input D2;
	input D1;
	input D0;
	input FCLK;
	input PCLK;
	input RESET;

	parameter GSREN = "false";
	parameter LSREN = "true";
endmodule

module OVIDEO(D6, D5, D4, D3, D2, D1, D0, FCLK, PCLK, RESET, Q);
	output Q;

	input D6;
	input D5;
	input D4;
	input D3;
	input D2;
	input D1;
	input D0;
	input FCLK;
	input PCLK;
	input RESET;

	parameter GSREN = "false";
	parameter LSREN = "true";
endmodule

module OSER16(D15, D14, D13, D12, D11, D10, 
D9, D8, D7, D6, D5, D4, D3, D2, D1, D0, FCLK, PCLK,
RESET, Q);
	output Q;

	input D15;
	input D14;
	input D13;
	input D12;
	input D11;
	input D10;
	input D9;
	input D8;
	input D7;
	input D6;
	input D5;
	input D4;
	input D3;
	input D2;
	input D1;
	input D0;
	input FCLK;
	input PCLK;
	input RESET;

	parameter GSREN = "false";
	parameter LSREN = "true";
endmodule

module IDES4(Q3, Q2, Q1, Q0, FCLK, PCLK,
RESET, CALIB, D);
	input D;
	input FCLK;
	input PCLK;
	input RESET;
	input CALIB;

	output Q3;
	output Q2;
	output Q1;
	output Q0;

	parameter GSREN = "false";
	parameter LSREN = "true";
endmodule

module IDES4_MEM (Q0, Q1, Q2, Q3, D, WADDR,
RADDR, CALIB, PCLK, FCLK, ICLK, RESET)  ;
parameter GSREN = "";
parameter LSREN = "";

input D, ICLK, FCLK, PCLK;
input [2:0] WADDR;
input [2:0] RADDR;
input CALIB, RESET;

output Q0,Q1,Q2,Q3;

parameter ID = "";
endmodule

module IDES8(Q7, Q6, Q5, Q4, Q3, Q2, Q1, Q0, FCLK, PCLK,
RESET, CALIB, D);
	input D;
	input FCLK;
	input PCLK;
	input RESET;
	input CALIB;

	output Q7;
	output Q6;
	output Q5;
	output Q4;
	output Q3;
	output Q2;
	output Q1;
	output Q0;

	parameter GSREN = "false";
	parameter LSREN = "true";
endmodule

module IDES10(Q9, Q8, Q7, Q6, Q5, Q4, Q3, Q2, Q1, Q0, FCLK, PCLK,
RESET, CALIB, D);
	input D;
	input FCLK;
	input PCLK;
	input RESET;
	input CALIB;

	output Q9;
	output Q8;
	output Q7;
	output Q6;
	output Q5;
	output Q4;
	output Q3;
	output Q2;
	output Q1;
	output Q0;

	parameter GSREN = "false";
	parameter LSREN = "true";
endmodule

module IVIDEO(Q6, Q5, Q4, Q3, Q2, Q1, Q0, FCLK, PCLK,
RESET, CALIB, D);
	input D;
	input FCLK;
	input PCLK;
	input RESET;
	input CALIB;

	output Q6;
	output Q5;
	output Q4;
	output Q3;
	output Q2;
	output Q1;
	output Q0;

	parameter GSREN = "false";
	parameter LSREN = "true";
endmodule

module IDES16(Q15, Q14, Q13, Q12, Q11, Q10, 
Q9, Q8, Q7, Q6, Q5, Q4, Q3, Q2, Q1, Q0, FCLK, PCLK,
RESET, CALIB, D);
	input D;
	input FCLK;
	input PCLK;
	input RESET;
	input CALIB;

	output Q15;
	output Q14;
	output Q13;
	output Q12;
	output Q11;
	output Q10;
	output Q9;
	output Q8;
	output Q7;
	output Q6;
	output Q5;
	output Q4;
	output Q3;
	output Q2;
	output Q1;
	output Q0;

	parameter GSREN = "false";
	parameter LSREN = "true";
endmodule

module IDDR(D, CLK, Q0, Q1);
	input D;
	input CLK;
	output Q0;
	output Q1;
	parameter Q0_INIT = 1'b0;
	parameter Q1_INIT = 1'b0;
endmodule

module IDDRC(D, CLK, CLEAR, Q0, Q1);
	input D;
	input CLK;
	input CLEAR;
	output Q0;
	output Q1;
	parameter Q0_INIT = 1'b0;
	parameter Q1_INIT = 1'b0;
endmodule

module DQS(DQSR90, DQSW0, DQSW270, RPOINT, WPOINT, RVALID, RBURST, RFLAG,
WFLAG, DQSIN, DLLSTEP, WSTEP, READ, RLOADN, RMOVE, RDIR, WLOADN, WMOVE, WDIR,
HOLD, RCLKSEL, PCLK, FCLK, RESET) ;
    input DQSIN,PCLK,FCLK,RESET;
    input [3:0] READ;
    input [2:0] RCLKSEL;
    input [7:0] DLLSTEP;
    input [7:0] WSTEP;
    input RLOADN, RMOVE, RDIR, WLOADN, WMOVE, WDIR, HOLD;

    output DQSR90, DQSW0, DQSW270;
    output [2:0] RPOINT, WPOINT;
    output RVALID,RBURST, RFLAG, WFLAG;

    parameter FIFO_MODE_SEL = "";
    parameter RD_PNTR = "";
    parameter DQS_MODE = "";
    parameter HWL = "";
    parameter GSREN = "";
    parameter ID = "";
endmodule

(* abc9_box, lib_whitebox *)
module ALU (SUM, COUT, I0, I1, I3, CIN);

input I0;
input I1;
input I3;
(* abc9_carry *) input CIN;
output SUM;
(* abc9_carry *) output COUT;

localparam ADD = 0;
localparam SUB = 1;
localparam ADDSUB = 2;
localparam NE = 3;
localparam GE = 4;
localparam LE = 5;
localparam CUP = 6;
localparam CDN = 7;
localparam CUPCDN = 8;
localparam MULT = 9;

parameter ALU_MODE = 0;

reg S, C;

specify
	(I0 => SUM) = (1043, 1432);
	(I1 => SUM) = (775, 1049);
	(I3 => SUM) = (751, 1010);
	(CIN => SUM) = (694, 811);
	(I0  => COUT) = (1010, 1380);
	(I1  => COUT) = (1021, 1505);
	(I3  => COUT) = (483, 792);
	(CIN => COUT) = (49, 82);
endspecify

assign SUM = S ^ CIN;
assign COUT = S? CIN : C;

always @* begin
	case (ALU_MODE)
		ADD: begin
			S = I0 ^ I1;
			C = I0;
		end
		SUB: begin
			S = I0 ^ ~I1;
			C = I0;
		end
		ADDSUB: begin
			S = I3? I0 ^ I1 : I0 ^ ~I1;
			C = I0;
		end
		NE: begin
			S = I0 ^ ~I1;
			C = 1'b1;
		end
		GE: begin
			S = I0 ^ ~I1;
			C = I0;
		end
		LE: begin
			S = ~I0 ^ I1;
			C = I1;
		end
		CUP: begin
			S = I0;
			C = 1'b0;
		end
		CDN: begin
			S = ~I0;
			C = 1'b1;
		end
		CUPCDN: begin
			S = I3? I0 : ~I0;
			C = I0;
		end
		MULT: begin
			S = (I0 & I1) ^ I3;
			C = I0 & I1;
		end
	endcase
end

endmodule

(* abc9_flop, lib_whitebox *)
module RAM16S1 (DO, DI, AD, WRE, CLK);

parameter INIT_0 = 16'h0000;

input [3:0] AD;
input DI;
output DO;
input CLK;
input WRE;

specify
	(AD *> DO) = (270, 405);
	$setup(DI, posedge CLK, 62);
	$setup(WRE, posedge CLK, 62);
	$setup(AD, posedge CLK, 62);
	(posedge CLK => (DO : 1'bx)) = (474, 565);
endspecify

reg [15:0] mem;

initial begin
	mem = INIT_0;
end

assign DO = mem[AD];

always @(posedge CLK) begin
	if (WRE) begin
		mem[AD] <= DI;
	end
end

endmodule

(* abc9_flop, lib_whitebox *)
module RAM16S2 (DO, DI, AD, WRE, CLK);

parameter INIT_0 = 16'h0000;
parameter INIT_1 = 16'h0000;

input [3:0] AD;
input [1:0] DI;
output [1:0] DO;
input CLK;
input WRE;

specify
	(AD *> DO) = (270, 405);
	$setup(DI, posedge CLK, 62);
	$setup(WRE, posedge CLK, 62);
	$setup(AD, posedge CLK, 62);
	(posedge CLK => (DO : 2'bx)) = (474, 565);
endspecify

reg [15:0] mem0, mem1;

initial begin
	mem0 = INIT_0;
	mem1 = INIT_1;
end

assign DO[0] = mem0[AD];
assign DO[1] = mem1[AD];

always @(posedge CLK) begin
	if (WRE) begin
		mem0[AD] <= DI[0];
		mem1[AD] <= DI[1];
	end
end

endmodule

(* abc9_flop, lib_whitebox *)
module RAM16S4 (DO, DI, AD, WRE, CLK);

parameter INIT_0 = 16'h0000;
parameter INIT_1 = 16'h0000;
parameter INIT_2 = 16'h0000;
parameter INIT_3 = 16'h0000;

input [3:0] AD;
input [3:0] DI;
output [3:0] DO;
input CLK;
input WRE;

specify
	(AD *> DO) = (270, 405);
	$setup(DI, posedge CLK, 62);
	$setup(WRE, posedge CLK, 62);
	$setup(AD, posedge CLK, 62);
	(posedge CLK => (DO : 4'bx)) = (474, 565);
endspecify

reg [15:0] mem0, mem1, mem2, mem3;

initial begin
	mem0 = INIT_0;
	mem1 = INIT_1;
	mem2 = INIT_2;
	mem3 = INIT_3;
end

assign DO[0] = mem0[AD];
assign DO[1] = mem1[AD];
assign DO[2] = mem2[AD];
assign DO[3] = mem3[AD];

always @(posedge CLK) begin
	if (WRE) begin
		mem0[AD] <= DI[0];
		mem1[AD] <= DI[1];
		mem2[AD] <= DI[2];
		mem3[AD] <= DI[3];
	end
end

endmodule


module RAM16SDP1 (DO, DI, WAD, RAD, WRE, CLK);

parameter INIT_0 = 16'h0000;

input [3:0] WAD;
input [3:0] RAD;
input DI;
output DO;
input CLK;
input WRE;

specify
	(RAD *> DO) = (270, 405);
	$setup(DI, posedge CLK, 62);
	$setup(WRE, posedge CLK, 62);
	$setup(WAD, posedge CLK, 62);
	(posedge CLK => (DO : 1'bx)) = (474, 565);
endspecify

reg [15:0] mem;

initial begin
	mem = INIT_0;
end

assign DO = mem[RAD];

always @(posedge CLK) begin
	if (WRE) begin
		mem[WAD] <= DI;
	end
end

endmodule


module RAM16SDP2 (DO, DI, WAD, RAD, WRE, CLK);

parameter INIT_0 = 16'h0000;
parameter INIT_1 = 16'h0000;

input [3:0] WAD;
input [3:0] RAD;
input [1:0] DI;
output [1:0] DO;
input CLK;
input WRE;

specify
	(RAD *> DO) = (270, 405);
	$setup(DI, posedge CLK, 62);
	$setup(WRE, posedge CLK, 62);
	$setup(WAD, posedge CLK, 62);
	(posedge CLK => (DO : 2'bx)) = (474, 565);
endspecify

reg [15:0] mem0, mem1;

initial begin
	mem0 = INIT_0;
	mem1 = INIT_1;
end

assign DO[0] = mem0[RAD];
assign DO[1] = mem1[RAD];

always @(posedge CLK) begin
	if (WRE) begin
		mem0[WAD] <= DI[0];
		mem1[WAD] <= DI[1];
	end
end

endmodule


module RAM16SDP4 (DO, DI, WAD, RAD, WRE, CLK);

parameter INIT_0 = 16'h0000;
parameter INIT_1 = 16'h0000;
parameter INIT_2 = 16'h0000;
parameter INIT_3 = 16'h0000;

input [3:0] WAD;
input [3:0] RAD;
input [3:0] DI;
output [3:0] DO;
input CLK;
input WRE;

specify
	(RAD *> DO) = (270, 405);
	$setup(DI, posedge CLK, 62);
	$setup(WRE, posedge CLK, 62);
	$setup(WAD, posedge CLK, 62);
	(posedge CLK => (DO : 4'bx)) = (474, 565);
endspecify

reg [15:0] mem0, mem1, mem2, mem3;

initial begin
	mem0 = INIT_0;
	mem1 = INIT_1;
	mem2 = INIT_2;
	mem3 = INIT_3;
end

assign DO[0] = mem0[RAD];
assign DO[1] = mem1[RAD];
assign DO[2] = mem2[RAD];
assign DO[3] = mem3[RAD];

always @(posedge CLK) begin
	if (WRE) begin
		mem0[WAD] <= DI[0];
		mem1[WAD] <= DI[1];
		mem2[WAD] <= DI[2];
		mem3[WAD] <= DI[3];
	end
end

endmodule
