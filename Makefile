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

PROCESSORS ?= 0

TOP                ?= compute_unit
TB_TOP             ?= tb_$(TOP)

# Source files
SRCS = $(wildcard rtl/**/*.sv)
TB_SRCS = $($(BENDER) scripts flist -n )
BENDER_DEPS:= Bender.lock Bender.yml Bender.local
TBS = $(basename $(notdir $(wildcard test/tb_*.sv)))

.PHONY: lint asic xilinx gowin-yosys clean tb_% tb-all

vendor/: $(BENDER_DEPS)
	$(BENDER) vendor init

bgpu-gowin: TOP := bgpu_soc
bgpu-gowin: gowin-eda-bgpu-wrapper gowin-eda-report gowin-eda-pnr gowin-eda-pnr-report

####################################################################################################
# Linting
####################################################################################################

# Lint using Verilator and Verible
lint: lint-verilator lint-verible

# Generate filelist for Verilator linting
verilator/verilator_lint.f: $(BENDER_DEPS) vendor/
	$(BENDER) script verilator $(BENDER_TARGET_LINT) > $@

# Lint using Verilator
lint-verilator: verilator/verilator_lint.f verilator/config.vlt $(SRCS) $(TB_SRCS)
	$(VERILATOR) -lint-only $(VERILATOR_FLAGS) $(VERILATOR_ARGS) -DPRIM_ASSERT_SV -f $< --timing --top $(TOP)

# Generate filelist for Verilator linting
verilator/verible_lint.f: $(BENDER_DEPS) vendor/
	$(BENDER) script flist -n $(BENDER_TARGET_LINT) -t verible > $@
	tr "\n" " " < $@ > $@.tmp
	mv $@.tmp $@

# Lint using Verible
lint-verible: verilator/verible_lint.f $(SRCS) $(TB_SRCS)
	$(VERIBLE_LINT) $(file < verilator/verible_lint.f)

####################################################################################################
# Verilator simulation
####################################################################################################

# Generate filelist for Verilator simulation
verilator/verilator_tb.f: $(BENDER_DEPS) vendor/
	$(BENDER) script verilator $(BENDER_TARGET_SIM) -t verilator -t tech_cells_generic_exclude_deprecated -t tech_cells_generic_exclude_xilinx_xpm -D PRIM_ASSERT_SV --no-default-target > $@

# Translate RTL to C++ using Verilator
verilator/obj_dir/V%.mk: verilator/verilator_tb.f verilator/config.vlt $(SRCS) $(TB_SRCS)
	$(VERILATOR) $(VERILATOR_FLAGS) $(VERILATOR_ARGS) -f $< --top $* --binary -j $(PROCESSORS) --timing --assert --trace --trace-structs --Mdir verilator/obj_dir

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
xilinx/vivado.f: $(BENDER_DEPS) vendor/
	$(BENDER) script vivado -t xilinx -t tech_cells_generic_exclude_tc_sram -t tech_cells_generic_exclude_tc_clk -t tech_cells_generic_exclude_xilinx_xpm -D SYNTHESIS -D PRIM_ASSERT_SV > $@

# Generate filelist for Yosys synthesis
xilinx/yosys.f: $(BENDER_DEPS) vendor/
	$(BENDER) script flist-plus -t xilinx_yosys -t tech_cells_generic_exclude_tc_sram -t tech_cells_generic_exclude_tc_clk -t tech_cells_generic_exclude_xilinx_xpm -D SYNTHESIS > $@

# Run Vivado synthesis
xilinx-vivado: xilinx/vivado.f $(SRCS) xilinx/scripts/vivado.tcl xilinx/src/dummy_constraints.xdc xilinx/run_vivado.sh
	time ./xilinx/run_vivado.sh $(VIVADO_SETTINGS) $(VIVADO) $(TOP) vivado.tcl

# Run Yosys synthesis
xilinx-yosys: xilinx/yosys.f $(SRCS) xilinx/scripts/yosys.tcl
	echo "set top_design $(TOP)"  >  xilinx/run_yosys.tcl
	echo "source xilinx/scripts/yosys.tcl" >> xilinx/run_yosys.tcl
	yosys -c xilinx/run_yosys.tcl -l xilinx/yosys.log -t

# Yosys report using Vivado
xilinx-yosys-report: xilinx/scripts/vivado_report.tcl xilinx/src/dummy_constraints.xdc xilinx/run_vivado_report.sh
	time ./xilinx/run_vivado_report.sh $(VIVADO_SETTINGS) $(VIVADO) $(TOP)

vivado-ips:	
	time ./xilinx/run_vivado.sh $(VIVADO_SETTINGS) $(VIVADO) $(TOP) vivado_ip.tcl

####################################################################################################
# ASIC Synthesis
####################################################################################################

# Generate filelist for Yosys synthesis
asic/yosys.f: $(BENDER_DEPS) vendor/
	$(BENDER) script flist-plus -t asic -D SYNTHESIS > $@

# Yosys Makefile
include asic/asic.mk

####################################################################################################
# Gowin Synthesis
####################################################################################################

gowin/gowin-yosys.f: $(BENDER_DEPS) vendor/
	$(BENDER) script flist-plus -t gowin_yosys -D SYNTHESIS -t tech_cells_generic_exclude_tc_sram > $@

gowin/gowin-eda.f: $(BENDER_DEPS) vendor/
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
	gowin/run_eda.sh ${GOWIN_EDA} gowin/run_eda.tcl

gowin-eda-bgpu-wrapper: TOP := bgpu_soc
gowin-eda-bgpu-wrapper: gowin/gowin-eda.f $(SRCS) gowin/scripts/eda_bgpu_wrapper.tcl
	mkdir -p gowin/out
	morty -f gowin/gowin-eda.f -D SYNTHESIS > gowin/out/pickled.sv
	gowin/run_eda.sh ${GOWIN_EDA} gowin/scripts/eda_bgpu_wrapper.tcl

gowin-eda-report:
	lynx gowin/out/$(TOP)/impl/gwsynthesis/$(TOP)_syn.rpt.html -dump -width 256 > gowin/gowin_eda_report.rpt
	sed -i 's/\&nbsp/     /g' gowin/gowin_eda_report.rpt
	sed -i '1,10d' gowin/gowin_eda_report.rpt
	grep -A 100 "Resource Usage Summary" gowin/gowin_eda_report.rpt 

gowin-eda-process-netlist: gowin/scripts/rename_ports.py gowin/scripts/process_eda_netlist.tcl
	echo "set top_design $(TOP)"  >  gowin/run_process.tcl
	echo "source gowin/scripts/process_eda_netlist.tcl" >> gowin/run_process.tcl
	yosys -c gowin/run_process.tcl -l gowin/gowin_process.log -t

gowin-yosys-gen-report: gowin/scripts/yosys_timing_eda.tcl
	echo "set top_design $(TOP)"  >  gowin/run_timing.tcl
	echo "source gowin/scripts/yosys_timing_eda.tcl" >> gowin/run_timing.tcl
	mkdir -p gowin/out
	gowin/run_eda.sh ${GOWIN_EDA} gowin/run_timing.tcl

gowin-yosys-report:
	lynx gowin/out/$(TOP)_yosys/impl/gwsynthesis/$(TOP)_yosys_syn.rpt.html -dump -width 256 > gowin/gowin_yosys_report.rpt
	sed -i 's/\&nbsp/     /g' gowin/gowin_yosys_report.rpt
	sed -i '1,10d' gowin/gowin_yosys_report.rpt
	grep -A 100 "Resource Usage Summary" gowin/gowin_yosys_report.rpt 

gowin-report:
	tail -n 100 gowin/gowin.log

gowin-eda-pnr:
	echo "set top_design $(TOP)"  >  gowin/run_pnr.tcl
	echo "source gowin/scripts/eda_pnr.tcl" >> gowin/run_pnr.tcl
	gowin/run_eda.sh ${GOWIN_EDA} gowin/run_pnr.tcl

gowin-eda-pnr-report:
	lynx gowin/out/$(TOP)/impl/pnr/$(TOP)_tr_content.html -dump -width 256 > gowin/gowin_eda_pnr_report.rpt
	sed -i 's/\&nbsp/     /g' gowin/gowin_eda_pnr_report.rpt
	sed -i '1,10d' gowin/gowin_eda_pnr_report.rpt
	head -n 128 gowin/gowin_eda_pnr_report.rpt

####################################################################################################
# Clean
####################################################################################################

clean: asic-clean gowin-clean xilinx-clean verilator-clean
	rm -f *.vcd
	rm -f *.out
	rm -f *.log
	rm -rf vendor

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
