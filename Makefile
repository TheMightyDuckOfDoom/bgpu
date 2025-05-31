# Copyright 2025 Tobias Senti
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# Tools
BENDER          ?= bender
VERILATOR       ?= verilator
VIVADO          ?= vivado
VIVADO_SETTINGS ?= /tools/Xilinx/Vivado/202?.?/settings64.sh
VERIBLE_LINT    ?= verible-verilog-lint

VERILATOR_FLAGS:= verilator/config.vlt -Wno-UNOPTFLAT
VERILATOR_ARGS ?= ""

# Bender Targets
BENDER_TARGET_LINT ?= verilator
BENDER_TARGET_SIM  ?= verilator

TOP                ?= compute_unit
TB_TOP             ?= tb_$(TOP)

# Source files
SRCS = $(wildcard rtl/**/*.sv)
TB_SRCS = $($(BENDER) scripts flist -n )
BENDER_DEPS:= Bender.lock Bender.yml

.PHONY: lint asic xilinx gowin clean tb_%

####################################################################################################
# Linting
####################################################################################################

# Lint using Verilator and Verible
lint: lint-verilator lint-verible

# Generate filelist for Verilator linting
verilator/verilator_lint.f: $(BENDER_DEPS)
	$(BENDER) script verilator -t $(BENDER_TARGET_LINT) > $@

# Lint using Verilator
lint-verilator: verilator/verilator_lint.f verilator/config.vlt $(SRCS) $(TB_SRCS)
	$(VERILATOR) -lint-only $(VERILATOR_FLAGS) $(VERILATOR_ARGS) -f $< --top $(TOP)

# Generate filelist for Verilator linting
verilator/verible_lint.f: $(BENDER_DEPS)
	$(BENDER) script flist -n -t $(BENDER_TARGET_LINT) > $@
	tr "\n" " " < $@ > $@.tmp
	mv $@.tmp $@

# Lint using Verible
lint-verible: verilator/verible_lint.f $(SRCS) $(TB_SRCS)
	$(VERIBLE_LINT) $(file < verilator/verible_lint.f)

####################################################################################################
# Verilator simulation
####################################################################################################

# Generate filelist for Verilator simulation
verilator/verilator_tb.f: $(BENDER_DEPS)
	$(BENDER) script verilator -t $(BENDER_TARGET_LINT) > $@

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
	$(BENDER) script vivado -t fpga -D SYNTHESIS > $@

# Run Vivado synthesis
xilinx: xilinx/vivado.f $(SRCS) xilinx/build.tcl xilinx/dummy_constraints.xdc xilinx/run.sh
	time ./xilinx/run.sh $(VIVADO_SETTINGS) $(VIVADO) $(TOP)

####################################################################################################
# ASIC Synthesis
####################################################################################################

# Generate filelist for Yosys synthesis
asic/yosys.f: $(BENDER_DEPS)
	$(BENDER) script flist-plus -t asic -D SYNTHESIS > $@

# Yosys Makefile
include asic/asic.mk

####################################################################################################
# Gowin Synthesis
####################################################################################################

gowin/gowin.f: $(BENDER_DEPS)
	$(BENDER) script flist-plus -t gowin -D SYNTHESIS -t tech_cells_generic_exclude_tc_sram > $@

gowin: gowin/gowin.f $(SRCS) gowin/build.tcl
	echo "set top_design $(TOP)"  >  gowin/run.tcl
	echo "source gowin/build.tcl" >> gowin/run.tcl
	yosys -c gowin/run.tcl -l gowin/gowin.log -t

gowin-report:
	tail -n 64 gowin/gowin.log

####################################################################################################
# Clean
####################################################################################################

clean: asic_clean
	rm -f  verilator/*.f
	rm -rf verilator/obj_dir
	rm -f  xilinx/*.f
	rm -f  xilinx/run.tcl
	rm -rf xilinx/.Xil
	rm -f  xilinx/*.log
	rm -f  xilinx/*.jou
	rm -f  gowin/*.f
	rm -f  gowin/*.log
	rm -f  gowin/run.tcl
