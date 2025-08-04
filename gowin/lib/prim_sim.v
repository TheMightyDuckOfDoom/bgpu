// ===========Oooo==========================================Oooo========
// =  Copyright (C) 2014-2025 Gowin Semiconductor Technology Co.,Ltd.
// =                     All rights reserved.
// =====================================================================
//
//  __      __      __
//  \ \    /  \    / /   [File name   ] prim_sim.v
//   \ \  / /\ \  / /    [Description ] GW5AT verilog functional simulation library
//    \ \/ /  \ \/ /     [Timestamp   ] Fri November 4 11:00:30 2022
//     \  /    \  /      [version     ] 1.9.10
//      \/      \/       
//
// ===========Oooo==========================================Oooo========

/* verilator lint_off SELRANGE */
/* verilator lint_off WIDTHEXPAND */
/* verilator lint_off WIDTHTRUNC */
module SP (DO, DI, BLKSEL, AD, WRE, CLK, CE, OCE, RESET);

parameter READ_MODE = 1'b0; // 1'b0: bypass mode; 1'b1: pipeline mode
parameter WRITE_MODE = 2'b00; // 2'b00: normal mode; 2'b01: write-through mode; 2'b10: read-before-write mode
parameter BIT_WIDTH = 32; // 1, 2, 4, 8, 16, 32
parameter BLK_SEL = 3'b000;
parameter RESET_MODE = "SYNC"; // SYNC, ASYNC
parameter INIT_RAM_00 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_01 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_02 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_03 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_04 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_05 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_06 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_07 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_08 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_09 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_0A = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_0B = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_0C = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_0D = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_0E = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_0F = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_10 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_11 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_12 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_13 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_14 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_15 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_16 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_17 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_18 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_19 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_1A = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_1B = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_1C = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_1D = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_1E = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_1F = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_20 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_21 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_22 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_23 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_24 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_25 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_26 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_27 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_28 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_29 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_2A = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_2B = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_2C = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_2D = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_2E = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_2F = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_30 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_31 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_32 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_33 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_34 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_35 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_36 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_37 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_38 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_39 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_3A = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_3B = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_3C = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_3D = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_3E = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_3F = 256'h0000000000000000000000000000000000000000000000000000000000000000;
input CLK, CE;
input OCE; // clock enable of memory output register
input RESET; // resets output registers, not memory contents
input WRE; // 1'b0: read enabled; 1'b1: write enabled
input [13:0] AD;
input [31:0] DI;
input [2:0] BLKSEL;
output [31:0] DO;

`ifdef BRAM_DEBUG
    initial begin : bram_debug
        integer f;
        string data, filename;

        filename = $sformatf("bram_%m.log");
        f = $fopen(filename, "w");

        data = $sformatf("READ_MODE=%b, WRITE_MODE=%b, BIT_WIDTH=%d, BLK_SEL=%b, RESET_MODE=%s",
                         READ_MODE, WRITE_MODE, BIT_WIDTH, BLK_SEL, RESET_MODE);
        $fwrite(f, "%s\n", data);
        $fflush(f);

        $display("SP %m: %s", data);

        while(1) begin
            @(posedge CLK);

            if(CE && BLK_SEL == BLKSEL) begin
                data = $sformatf("time: %t, AD=%h, WRE=%b, DI=%h, DO=%h", $time(), AD, WRE, DI, DO);
                $fwrite(f, "%s\n", data);
                $fflush(f);
            end
        end
    end : bram_debug
`endif

initial assert(BIT_WIDTH inside {1, 2, 4, 8, 16, 32})
    else $error("SP %m: BIT_WIDTH(%d) must be one of 1, 2, 4, 8, 16, or 32", BIT_WIDTH);

reg [31:0] pl_reg,pl_reg_async,pl_reg_sync;
reg [31:0] bp_reg,bp_reg_async,bp_reg_sync;
reg bs_en;
wire pce;
reg [16383:0] ram_MEM = {INIT_RAM_3F, INIT_RAM_3E, INIT_RAM_3D, INIT_RAM_3C,INIT_RAM_3B, INIT_RAM_3A, INIT_RAM_39, INIT_RAM_38,INIT_RAM_37, INIT_RAM_36, INIT_RAM_35, INIT_RAM_34,INIT_RAM_33, INIT_RAM_32, INIT_RAM_31, INIT_RAM_30,INIT_RAM_2F, INIT_RAM_2E, INIT_RAM_2D, INIT_RAM_2C,INIT_RAM_2B, INIT_RAM_2A, INIT_RAM_29, INIT_RAM_28,INIT_RAM_27, INIT_RAM_26, INIT_RAM_25, INIT_RAM_24,INIT_RAM_23, INIT_RAM_22, INIT_RAM_21, INIT_RAM_20,INIT_RAM_1F, INIT_RAM_1E, INIT_RAM_1D, INIT_RAM_1C,INIT_RAM_1B, INIT_RAM_1A, INIT_RAM_19, INIT_RAM_18,INIT_RAM_17, INIT_RAM_16, INIT_RAM_15, INIT_RAM_14,INIT_RAM_13, INIT_RAM_12, INIT_RAM_11, INIT_RAM_10,INIT_RAM_0F, INIT_RAM_0E, INIT_RAM_0D, INIT_RAM_0C, INIT_RAM_0B, INIT_RAM_0A, INIT_RAM_09, INIT_RAM_08,INIT_RAM_07, INIT_RAM_06, INIT_RAM_05, INIT_RAM_04,INIT_RAM_03, INIT_RAM_02, INIT_RAM_01, INIT_RAM_00};
reg [BIT_WIDTH-1:0] mem_t;
reg mc;
reg [13:0] addr;
integer dwidth = BIT_WIDTH;
integer awidth; // ADDR_WIDTH

initial begin
    bp_reg = 0;
    pl_reg = 0;
    bp_reg_async = 0;
    bp_reg_sync = 0;
    pl_reg_async = 0;
    pl_reg_sync = 0;
    mc = 1'b0;
end

initial begin
	case(dwidth)
		1: awidth = 14;
		2: awidth = 13;
		4: awidth = 12;
		8: awidth = 11;
		16: awidth = 10;
		32: awidth = 9;
		default: begin
			$error ("%m: Unsupported data width (%d)\n", dwidth);
		end
	endcase
end

assign DO = (READ_MODE == 1'b0)? bp_reg : pl_reg;

assign pce = CE && bs_en;   
always @ (BLKSEL)
begin
	if(BLKSEL == BLK_SEL) begin
		bs_en = 1;
	end else begin
		bs_en = 0;
	end  	
end

always@(awidth,AD,WRE,mc)begin
	if(awidth==14)begin
		addr[13:0] = AD[13:0];
		mem_t[0] =ram_MEM[addr];
	end
	else if(awidth==13)begin
		addr[13:0] = {AD[13:1],1'b0};
		mem_t[1:0] ={ram_MEM[addr+1],ram_MEM[addr]};
	end
	else if(awidth==12)begin
		addr[13:0] = {AD[13:2],2'b00};
		mem_t[3:0] ={ram_MEM[addr+3],ram_MEM[addr+2],ram_MEM[addr+1],ram_MEM[addr]};
	end
	else if(awidth==11)begin
		addr[13:0] = {AD[13:3],3'b000};
		mem_t[7:0] ={ram_MEM[addr+7],ram_MEM[addr+6],ram_MEM[addr+5],ram_MEM[addr+4],ram_MEM[addr+3],ram_MEM[addr+2],ram_MEM[addr+1],ram_MEM[addr]};
	end
	else if(awidth==10)begin
		addr[13:0] = {AD[13:4],4'b0000};
		mem_t[15:0] ={ram_MEM[addr+15],ram_MEM[addr+14],ram_MEM[addr+13],ram_MEM[addr+12],ram_MEM[addr+11],ram_MEM[addr+10],ram_MEM[addr+9],ram_MEM[addr+8],ram_MEM[addr+7],ram_MEM[addr+6],ram_MEM[addr+5],ram_MEM[addr+4],ram_MEM[addr+3],ram_MEM[addr+2],ram_MEM[addr+1],ram_MEM[addr]};
	end
	else if(awidth==9)begin
		addr[13:0] = {AD[13:5],5'b00000};
		mem_t[31:0]={ram_MEM[addr+31],ram_MEM[addr+30],ram_MEM[addr+29],ram_MEM[addr+28],ram_MEM[addr+27],ram_MEM[addr+26],ram_MEM[addr+25],ram_MEM[addr+24],ram_MEM[addr+23],ram_MEM[addr+22],ram_MEM[addr+21],ram_MEM[addr+20],ram_MEM[addr+19],ram_MEM[addr+18],ram_MEM[addr+17],ram_MEM[addr+16],ram_MEM[addr+15],ram_MEM[addr+14],ram_MEM[addr+13],ram_MEM[addr+12],ram_MEM[addr+11],ram_MEM[addr+10],ram_MEM[addr+9],ram_MEM[addr+8],ram_MEM[addr+7],ram_MEM[addr+6],ram_MEM[addr+5],ram_MEM[addr+4],ram_MEM[addr+3],ram_MEM[addr+2],ram_MEM[addr+1],ram_MEM[addr]};
	end
end

//write and read
always @(posedge CLK) begin
	if (pce) begin
    	if(WRE) begin
		    if(dwidth==1)
			    ram_MEM[addr] <= DI[0];
			else if(dwidth==2)
				{ram_MEM[addr+1],ram_MEM[addr]}<=DI[BIT_WIDTH-1:0];
			else if(dwidth==4)
				{ram_MEM[addr+3],ram_MEM[addr+2],ram_MEM[addr+1],ram_MEM[addr]}<=DI[BIT_WIDTH-1:0];
			else if(dwidth==8)
				{ram_MEM[addr+7],ram_MEM[addr+6],ram_MEM[addr+5],ram_MEM[addr+4],ram_MEM[addr+3],ram_MEM[addr+2],ram_MEM[addr+1],ram_MEM[addr]}<=DI[7:0];

			else if(dwidth==16) begin
				if(AD[0] == 1'b1)
					{ram_MEM[addr+7],ram_MEM[addr+6],ram_MEM[addr+5],ram_MEM[addr+4],ram_MEM[addr+3],ram_MEM[addr+2],ram_MEM[addr+1],ram_MEM[addr]} <= DI[7:0];
				if(AD[1] == 1'b1)
					{ram_MEM[addr+15],ram_MEM[addr+14],ram_MEM[addr+13],ram_MEM[addr+12],ram_MEM[addr+11],ram_MEM[addr+10],ram_MEM[addr+9],ram_MEM[addr+8]} <= DI[15:8];
			end
			else if(dwidth==32) begin
				if(AD[0] == 1'b1)
					{ram_MEM[addr+7],ram_MEM[addr+6],ram_MEM[addr+5],ram_MEM[addr+4],ram_MEM[addr+3],ram_MEM[addr+2],ram_MEM[addr+1],ram_MEM[addr]}<=DI[7:0];
				if(AD[1] == 1'b1)
					{ram_MEM[addr+15],ram_MEM[addr+14],ram_MEM[addr+13],ram_MEM[addr+12],ram_MEM[addr+11],ram_MEM[addr+10],ram_MEM[addr+9],ram_MEM[addr+8]}<=DI[15:8];
				if(AD[2] == 1'b1)
					{ram_MEM[addr+23],ram_MEM[addr+22],ram_MEM[addr+21],ram_MEM[addr+20],ram_MEM[addr+19],ram_MEM[addr+18],ram_MEM[addr+17],ram_MEM[addr+16]} <= DI[23:16];	
				if(AD[3] == 1'b1)
					{ram_MEM[addr+31],ram_MEM[addr+30],ram_MEM[addr+29],ram_MEM[addr+28],ram_MEM[addr+27],ram_MEM[addr+26],ram_MEM[addr+25],ram_MEM[addr+24]} <= DI[31:24];	
			end
		    mc <= ~mc;
        end
	end
end	

always @ (bp_reg_async or bp_reg_sync or pl_reg_async or pl_reg_sync) begin
    if(RESET_MODE == "ASYNC") begin
        bp_reg <= bp_reg_async;
        pl_reg <= pl_reg_async;
    end
    else begin
        bp_reg <= bp_reg_sync;
        pl_reg <= pl_reg_sync;
    end
end

always @(posedge CLK or posedge RESET) begin
	if (RESET) begin
		bp_reg_async <= 0;
	end else begin
		if (pce) begin
    	    if(WRE) begin	
				if (WRITE_MODE == 2'b01) begin
					bp_reg_async[BIT_WIDTH-1:0] <= mem_t[BIT_WIDTH-1:0];
                    if(dwidth <= 8) begin
					    bp_reg_async[BIT_WIDTH-1:0] <= DI[BIT_WIDTH-1:0];                       
                    end else if(dwidth==16) begin
						if(AD[0] == 1'b1)
							bp_reg_async[7:0] <= DI[7:0];
						if(AD[1] == 1'b1)
                            bp_reg_async[15:8] <= DI[15:8];                        
				    end else if(dwidth==32) begin
						if(AD[0] == 1'b1)
                            bp_reg_async[7:0]  <= DI[7:0];
						if(AD[1] == 1'b1)
                            bp_reg_async[15:8] <= DI[15:8];
						if(AD[2] == 1'b1)
                            bp_reg_async[23:16] <= DI[23:16];	
						if(AD[3] == 1'b1)
                            bp_reg_async[31:24] <= DI[31:24];
			        end
				end

				if (WRITE_MODE == 2'b10) begin
					bp_reg_async[BIT_WIDTH-1:0] <= mem_t[BIT_WIDTH-1:0];
				end
				
			end else begin // WRE==0, read
				bp_reg_async[BIT_WIDTH-1:0] <= mem_t[BIT_WIDTH-1:0];
			end
		end
	end
end	

always @(posedge CLK) begin
	if (RESET) begin
		bp_reg_sync <= 0;
	end else begin
		if (pce) begin
    	    if(WRE) begin	
				if (WRITE_MODE == 2'b01) begin
					bp_reg_sync[BIT_WIDTH-1:0] <= mem_t[BIT_WIDTH-1:0];
                    if(dwidth <= 8) begin
					    bp_reg_sync[BIT_WIDTH-1:0] <= DI[BIT_WIDTH-1:0];                       
                    end else if(dwidth==16) begin
						if(AD[0] == 1'b1)
							bp_reg_sync[7:0] <= DI[7:0];
						if(AD[1] == 1'b1)
                            bp_reg_sync[15:8] <= DI[15:8];                        
				    end else if(dwidth==32) begin
						if(AD[0] == 1'b1)
                            bp_reg_sync[7:0]  <= DI[7:0];
						if(AD[1] == 1'b1)
                            bp_reg_sync[15:8] <= DI[15:8];
						if(AD[2] == 1'b1)
                            bp_reg_sync[23:16] <= DI[23:16];	
						if(AD[3] == 1'b1)
                            bp_reg_sync[31:24] <= DI[31:24];
			        end
				end

				if (WRITE_MODE == 2'b10) begin
					bp_reg_sync[BIT_WIDTH-1:0] <= mem_t[BIT_WIDTH-1:0];
				end
				
			end else begin // WRE==0, read
				bp_reg_sync[BIT_WIDTH-1:0] <= mem_t[BIT_WIDTH-1:0];
			end
		end
	end
end	

always @(posedge CLK or posedge RESET) begin
	if (RESET) begin
		pl_reg_async <= 0;
	end else begin
		if(OCE) begin
			pl_reg_async <= bp_reg;
		end
	end
end

always @(posedge CLK) begin
	if (RESET) begin
		pl_reg_sync <= 0;
	end else begin
		if(OCE) begin
			pl_reg_sync <= bp_reg;
		end
	end
end	

endmodule  // SP: single port 16k Block SRAM

// MULT12X12
module MULT12X12 (DOUT, A, B, CLK, CE, RESET);

parameter AREG_CLK = "BYPASS"; // "BYPASS","CLK0","CLK1"
parameter AREG_CE = "CE0"; // "CE0","CE1"
parameter AREG_RESET = "RESET0"; //"RESET0", "RESET1"

parameter BREG_CLK = "BYPASS"; // "BYPASS","CLK0","CLK1"
parameter BREG_CE = "CE0"; // "CE0","CE1"
parameter BREG_RESET = "RESET0"; //"RESET0", "RESET1"

parameter PREG_CLK = "BYPASS"; // "BYPASS","CLK0","CLK1"
parameter PREG_CE = "CE0"; // "CE0","CE1"
parameter PREG_RESET = "RESET0"; //"RESET0", "RESET1"

parameter OREG_CLK = "BYPASS"; // "BYPASS","CLK0","CLK1"
parameter OREG_CE = "CE0"; // "CE0","CE1"
parameter OREG_RESET = "RESET0"; //"RESET0", "RESET1"

parameter MULT_RESET_MODE = "SYNC";// SYNC,ASYNC

output [23:0] DOUT;
input  [11:0] A, B;
input  [1:0] CLK, CE, RESET;

reg A_CLK,A_CE,A_RESET,B_CLK,B_CE,B_RESET,P_CLK,P_CE,P_RESET,O_CLK,O_CE,O_RESET;
reg [11:0] ina_reg_async,ina_reg_sync,ina,ina_reg;
reg [11:0] inb_reg_async,inb_reg_sync,inb,inb_reg;
wire [23:0] a0,b0,mult_out0;
reg [23:0] out0_reg_async,out0_reg_sync,out0,out0_reg;
wire [23:0] m_out0;
reg [23:0] out_reg_async,out_reg_sync,out_reg,d_out;

wire grstn = 1'b1; // No global reset


    always @(ina_reg_async or ina_reg_sync or inb_reg_async or inb_reg_sync or out0_reg_async or out0_reg_sync or out_reg_sync or out_reg_async)
    begin
        if (MULT_RESET_MODE == "ASYNC")
        begin
            ina_reg <= ina_reg_async;
            inb_reg <= inb_reg_async;
            out0_reg <= out0_reg_async;
            out_reg <= out_reg_async;
        end
        else if (MULT_RESET_MODE == "SYNC")
        begin
            ina_reg <= ina_reg_sync;
            inb_reg <= inb_reg_sync;
            out0_reg <= out0_reg_sync;
            out_reg <= out_reg_sync;
        end
    end

    //clk,ce,reset mux
    //AREG
    always @(CLK)
    begin
        if (AREG_CLK == "CLK0")
            A_CLK = CLK[0];
        else if (AREG_CLK == "CLK1")
            A_CLK = CLK[1];
    end

    always @(CE)
    begin
        if (AREG_CE == "CE0")
            A_CE = CE[0];
        else if (AREG_CE == "CE1")
            A_CE = CE[1];
    end

    always @(RESET)
    begin
        if (AREG_RESET == "RESET0")
            A_RESET = RESET[0];
        else if (AREG_RESET == "RESET1")
            A_RESET = RESET[1];
    end

    //BREG
    always @(CLK)
    begin
        if (BREG_CLK == "CLK0")
            B_CLK = CLK[0];
        else if (BREG_CLK == "CLK1")
            B_CLK = CLK[1];
    end

    always @(CE)
    begin
        if (BREG_CE == "CE0")
            B_CE = CE[0];
        else if (BREG_CE == "CE1")
            B_CE = CE[1];
    end

    always @(RESET)
    begin
        if (BREG_RESET == "RESET0")
            B_RESET = RESET[0];
        else if (BREG_RESET == "RESET1")
            B_RESET = RESET[1];
    end

    //PREG
    always @(CLK)
    begin
        if (PREG_CLK == "CLK0")
            P_CLK = CLK[0];
        else if (PREG_CLK == "CLK1")
            P_CLK = CLK[1];
    end

    always @(CE)
    begin
        if (PREG_CE == "CE0")
            P_CE = CE[0];
        else if (PREG_CE == "CE1")
            P_CE = CE[1];
    end

    always @(RESET)
    begin
        if (PREG_RESET == "RESET0")
            P_RESET = RESET[0];
        else if (PREG_RESET == "RESET1")
            P_RESET = RESET[1];
    end

    //OREG
    always @(CLK)
    begin
        if (OREG_CLK == "CLK0")
            O_CLK = CLK[0];
        else if (OREG_CLK == "CLK1")
            O_CLK = CLK[1];
    end

    always @(CE)
    begin
        if (OREG_CE == "CE0")
            O_CE = CE[0];
        else if (OREG_CE == "CE1")
            O_CE = CE[1];
    end

    always @(RESET)
    begin
        if (OREG_RESET == "RESET0")
            O_RESET = RESET[0];
        else if (OREG_RESET == "RESET1")
            O_RESET = RESET[1];
    end

    // in reg
    always @(posedge A_CLK or posedge A_RESET or negedge grstn)
    begin
        if (!grstn) begin
            ina_reg_async <= 0;
        end else if (A_RESET == 1'b1)
        begin
            ina_reg_async <= 0;
        end
        else if (A_CE == 1'b1)
        begin
            ina_reg_async <= A;
        end
    end

    always @(posedge A_CLK or negedge grstn)
    begin
        if (!grstn) begin
            ina_reg_sync <= 0; 
        end else if (A_RESET == 1'b1)
        begin
            ina_reg_sync <= 0;
        end
        else if (A_CE == 1'b1)
        begin
            ina_reg_sync <= A;
        end
    end

    always @(A or ina_reg)
    begin
        if (AREG_CLK == "BYPASS")
        begin
            ina = A;
        end else
        begin
            ina = ina_reg;
        end
    end

    always @(posedge B_CLK or posedge B_RESET or negedge grstn)
    begin
        if (!grstn) begin
            inb_reg_async <= 0;
        end else if (B_RESET == 1'b1)
        begin
            inb_reg_async <= 0;
        end
        else if (B_CE == 1'b1)
        begin
            inb_reg_async <= B;
        end
    end

    always @(posedge B_CLK or negedge grstn)
    begin
        if (!grstn) begin
            inb_reg_sync <= 0; 
        end else if (B_RESET == 1'b1)
        begin
            inb_reg_sync <= 0;
        end
        else if (B_CE == 1'b1)
        begin
            inb_reg_sync <= B;
        end
    end

    always @(B or inb_reg)
    begin
        if (BREG_CLK == "BYPASS")
        begin
            inb = B;
        end else
        begin
            inb = inb_reg;
        end
    end

    assign a0[23:0] = {{12{ina[11]}},ina[11:0]};
    assign b0[23:0] = {{12{inb[11]}},inb[11:0]};

    assign mult_out0 = a0 * b0 ;

    // pipeline reg
    always @(posedge P_CLK or posedge P_RESET or negedge grstn)
    begin
        if (!grstn) begin
            out0_reg_async <= 0;
        end else if (P_RESET == 1'b1)
        begin
            out0_reg_async <= 0;
        end
        else if (P_CE == 1'b1)
        begin
            out0_reg_async <= mult_out0;
        end
    end

    always @(posedge P_CLK or negedge grstn)
    begin
        if (!grstn) begin
            out0_reg_sync <= 0;
        end else if (P_RESET == 1'b1)
        begin
            out0_reg_sync <= 0;
        end
        else if (P_CE == 1'b1)
        begin
            out0_reg_sync <= mult_out0;
        end
    end

    always @(mult_out0 or out0_reg)
    begin
        if (PREG_CLK == "BYPASS")
        begin
            out0 = mult_out0;
        end else
        begin
            out0 = out0_reg;
        end
    end

    // output reg
    always @(posedge O_CLK or posedge O_RESET or negedge grstn)
    begin
        if (!grstn) begin
            out_reg_async <= 0;
        end else if (O_RESET == 1'b1)
        begin
            out_reg_async <= 0;
        end
        else if (O_CE == 1'b1)
        begin
            out_reg_async <= out0;
        end
    end

    always @(posedge O_CLK or negedge grstn)
    begin
        if (!grstn) begin
            out_reg_sync <= 0;
        end else if (O_RESET == 1'b1)
        begin
            out_reg_sync <= 0;
        end
        else if (O_CE == 1'b1)
        begin
            out_reg_sync <= out0;
        end
    end

    always @(out0 or out_reg)
    begin
        if (OREG_CLK == "BYPASS")
        begin
            d_out = out0;
        end else
        begin
            d_out = out_reg;
        end
    end

    assign DOUT = d_out[23:0];

endmodule

/* verilator lint_off SELRANGE */
/* verilator lint_off WIDTHEXPAND */
/* verilator lint_off WIDTHTRUNC */
