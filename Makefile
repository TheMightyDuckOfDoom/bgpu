# Copyright 2025 Tobias Senti
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# Tools
BENDER          ?= bender
VERILATOR       ?= verilator
VIVADO          ?= vivado
VIVADO_SETTINGS ?= /tools/Xilinx/202?.?/Vivado/settings64.sh
VERIBLE_LINT    ?= verible-verilog-lint

VERILATOR_FLAGS:= verilator/config.vlt -Wno-UNOPTFLAT -Wno-TIMESCALEMOD
VERILATOR_ARGS ?= ""

GOWIN_EDA ?= /tools/Gowin/IDE_1.9.11.02

# Bender Targets
BENDER_TARGET_LINT ?= -t sim
BENDER_TARGET_SIM  ?= -t sim

TOP                ?= compute_unit
TB_TOP             ?= tb_$(TOP)

# Source files
SRCS = $(wildcard rtl/**/*.sv)
TB_SRCS = $($(BENDER) scripts flist -n )
BENDER_DEPS:= Bender.lock Bender.yml
TBS = $(basename $(notdir $(wildcard test/tb_*.sv)))

.PHONY: lint asic xilinx gowin-yosys clean tb_% tb-all

####################################################################################################
# Linting
####################################################################################################

# Lint using Verilator and Verible
lint: lint-verilator lint-verible

# Generate filelist for Verilator linting
verilator/verilator_lint.f: $(BENDER_DEPS)
	$(BENDER) script verilator $(BENDER_TARGET_LINT) > $@

# Lint using Verilator
lint-verilator: verilator/verilator_lint.f verilator/config.vlt $(SRCS) $(TB_SRCS)
	$(VERILATOR) -lint-only $(VERILATOR_FLAGS) $(VERILATOR_ARGS) -f $< --top $(TOP)

# Generate filelist for Verilator linting
verilator/verible_lint.f: $(BENDER_DEPS)
	$(BENDER) script flist -n $(BENDER_TARGET_LINT) > $@
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
	$(BENDER) script verilator $(BENDER_TARGET_SIM) > $@

# Translate RTL to C++ using Verilator
verilator/obj_dir/V%.mk: verilator/verilator_tb.f verilator/config.vlt $(SRCS) $(TB_SRCS)
	$(VERILATOR) $(VERILATOR_FLAGS) $(VERILATOR_ARGS) -f $< --top $* --binary -j 0 --timing --assert --trace --trace-structs --Mdir verilator/obj_dir

# Build the testbench
verilator/obj_dir/V%: verilator/obj_dir/V%.mk
	make -C verilator/obj_dir -j -f V$*.mk V$*

# Run the testbench
tb_%: verilator/obj_dir/Vtb_%
	./$<

# Run all testbenches
tb-all: $(TBS)
	echo $(TBS)

####################################################################################################
# Xilinx Synthesis
####################################################################################################

# Generate filelist for Vivado synthesis
xilinx/vivado.f: $(BENDER_DEPS)
	$(BENDER) script vivado -t xilinx -t tech_cells_generic_exclude_tc_sram -D SYNTHESIS > $@

# Generate filelist for Yosys synthesis
xilinx/yosys.f: $(BENDER_DEPS)
	$(BENDER) script flist-plus -t xilinx_yosys -t tech_cells_generic_exclude_tc_sram -D SYNTHESIS > $@

# Run Vivado synthesis
xilinx-vivado: xilinx/vivado.f $(SRCS) xilinx/scripts/vivado.tcl xilinx/dummy_constraints.xdc xilinx/run_vivado.sh
	time ./xilinx/run_vivado.sh $(VIVADO_SETTINGS) $(VIVADO) $(TOP)

# Run Yosys synthesis
xilinx-yosys: xilinx/yosys.f $(SRCS) xilinx/scripts/yosys.tcl
	echo "set top_design $(TOP)"  >  xilinx/run_yosys.tcl
	echo "source xilinx/scripts/yosys.tcl" >> xilinx/run_yosys.tcl
	yosys -c xilinx/run_yosys.tcl -l xilinx/yosys.log -t

# Show Yosys report
xilinx-yosys-report:
	tail -n 32 xilinx/yosys.log

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

gowin/gowin-yosys.f: $(BENDER_DEPS)
	$(BENDER) script flist-plus -t gowin_yosys -D SYNTHESIS -t tech_cells_generic_exclude_tc_sram > $@

gowin/gowin-eda.f: $(BENDER_DEPS)
	$(BENDER) sources -f -t gowin_eda -t tech_cells_generic_exclude_tc_sram > $@

gowin-yosys: gowin/gowin-yosys.f $(SRCS) gowin/scripts/yosys.tcl
	echo "set top_design $(TOP)"  >  gowin/run_yosys.tcl
	echo "source gowin/scripts/yosys.tcl" >> gowin/run_yosys.tcl
	yosys -c gowin/run_yosys.tcl -l gowin/gowin.log -t

gowin-eda: gowin/gowin-eda.f $(SRCS) gowin/scripts/eda.tcl
	echo "set top_design $(TOP)"  >  gowin/run_eda.tcl
	echo "source gowin/scripts/eda.tcl" >> gowin/run_eda.tcl
	mkdir -p gowin/out
	morty -f gowin/gowin-eda.f -D SYNTHESIS --top $(TOP) > gowin/out/pickled.sv
	LD_LIBRARY_PATH=${GOWIN_EDA}/lib ${GOWIN_EDA}/bin/gw_sh gowin/run_eda.tcl

gowin-eda-report:
	lynx gowin/out/$(TOP)/impl/gwsynthesis/$(TOP)_syn.rpt.html -dump -width 256 > gowin/gowin_eda_report.rpt
	sed -i 's/\&nbsp/     /g' gowin/gowin_eda_report.rpt
	sed -i '1,10d' gowin/gowin_eda_report.rpt
	grep -A 43 "Resource Usage Summary" gowin/gowin_eda_report.rpt 

gowin-yosys-gen-report: gowin/scripts/yosys_timing_eda.tcl
	echo "set top_design $(TOP)"  >  gowin/run_timing.tcl
	echo "source gowin/scripts/yosys_timing_eda.tcl" >> gowin/run_timing.tcl
	mkdir -p gowin/out
	LD_LIBRARY_PATH=${GOWIN_EDA}/lib ${GOWIN_EDA}/bin/gw_sh gowin/run_timing.tcl

gowin-yosys-report:
	lynx gowin/out/$(TOP)_yosys/impl/gwsynthesis/$(TOP)_yosys_syn.rpt.html -dump -width 256 > gowin/gowin_yosys_report.rpt
	sed -i 's/\&nbsp/     /g' gowin/gowin_yosys_report.rpt
	sed -i '1,10d' gowin/gowin_yosys_report.rpt
	grep -A 43 "Resource Usage Summary" gowin/gowin_yosys_report.rpt 

gowin-report:
	tail -n 64 gowin/gowin.log

####################################################################################################
# Clean
####################################################################################################

clean: asic-clean gowin-clean xilinx-clean verilator-clean

verilator-clean:
	rm -f  verilator/*.f
	rm -rf verilator/obj_dir

xilinx-clean:
	rm -f  xilinx/*.f
	rm -f  xilinx/run_*.tcl
	rm -rf xilinx/.Xil
	rm -f  xilinx/*.log
	rm -f  xilinx/*.jou
	rm -rf xilinx/out
	rm -rf xilinx/cong
	rm -f  xilinx/clockInfo.txt

gowin-clean:
	rm -f  gowin/*.f
	rm -f  gowin/*.log
	rm -f  gowin/*.rpt
	rm -f  gowin/run*.tcl
	rm -rf gowin/out
