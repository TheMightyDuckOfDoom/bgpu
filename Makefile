# Copyright 2025 Tobias Senti
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# Source files
SRCS = $(wildcard rtl/**/*.sv)
TB_SRCS = $(wildcard test/*.sv)

# Tools
BENDER          ?= bender
VERILATOR       ?= verilator
VIVADO          ?= vivado
VIVADO_SETTINGS ?= /tools/Xilinx/Vivado/202?.?/settings64.sh
VERIBLE_LINT    ?= verible-verilog-lint

VERILATOR_FLAGS:= verilator/config.vlt
VERILATOR_ARGS ?=

BENDER_DEPS:= Bender.lock Bender.yml

TOP ?= compute_unit
TB_TOP ?= tb_$(TOP)

@PHONY: lint xilinx clean

####################################################################################################
# Linting
####################################################################################################

# Lint using Verilator and Verible
lint: lint-verilator lint-verible

# Generate filelist for Verilator linting
verilator/verilator.f: $(BENDER_DEPS)
	$(BENDER) script verilator > $@

# Lint using Verilator
lint-verilator: verilator/verilator.f verilator/config.vlt $(SRCS) $(TB_SRCS)
	$(VERILATOR) -lint-only $(VERILATOR_FLAGS) -f $< --top $(TOP)

# Lint using Verible
lint-verible: $(SRCS) $(TB_SRCS)
	$(VERIBLE_LINT) $(SRCS) $(TB_SRCS)

####################################################################################################
# Verilator simulation
####################################################################################################

# Generate filelist for Verilator simulation
verilator/verilator_tb.f: $(BENDER_DEPS)
	$(BENDER) script verilator -t verilator > $@

# Translate RTL to C++ using Verilator
verilator/obj_dir/V%.mk: verilator/verilator_tb.f verilator/config.vlt $(SRCS) $(TB_SRCS)
	$(VERILATOR) $(VERILATOR_FLAGS) $(VERILATOR_ARGS) -f $< --top $* --binary -j 0 --timing --assert --trace --trace-structs --Mdir verilator/obj_dir

# Build the testbench
verilator/obj_dir/V%: verilator/obj_dir/V%.mk
	make -C verilator/obj_dir -j -f V$*.mk V$*

# Run the testbench
tb_%: verilator/obj_dir/Vtb_%
	./$<

####################################################################################################
# Xilinx Synthesis
####################################################################################################

# Generate filelist for Vivado synthesis
xilinx/vivado.f: $(BENDER_DEPS)
	$(BENDER) script vivado > $@

# Run Vivado synthesis
xilinx: xilinx/vivado.f $(SRCS) xilinx/build.tcl xilinx/dummy_constraints.xdc xilinx/run.sh
	time ./xilinx/run.sh $(VIVADO_SETTINGS) $(VIVADO) $(TOP)

####################################################################################################
# Yosys Synthesis
####################################################################################################

# Generate filelist for Yosys synthesis
yosys/yosys.f: $(BENDER_DEPS)
	$(BENDER) script flist-plus -DSYNTHESIS > yosys/yosys.f

# Yosys Makefile
include yosys/yosys.mk

####################################################################################################
# Clean
####################################################################################################

clean:
	rm -f  yosys/*.f
	rm -f  yosys/*.log
	rm -rf yosys/out
	rm -rf yosys/reports
	rm -rf yosys/tmp
	rm -f  verilator/*.f
	rm -rf verilator/obj_dir
	rm -f  xilinx/*.f
	rm -f  xilinx/run.tcl
	rm -rf xilinx/.Xil
	rm -f  xilinx/*.log
	rm -f  xilinx/*.jou
