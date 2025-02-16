# Tobias Senti, Feb 2025

# Source files
SRCS = $(wildcard src/*.sv)

# Tools
BENDER          ?= bender
VERILATOR       ?= verilator
VIVADO          ?= vivado
VIVADO_SETTINGS ?= /tools/Xilinx/Vivado/202?.?/settings64.sh

TOP ?= compute_unit

@PHONY: lint synth clean

# Targets
verilator.f: Bender.lock Bender.yml
	$(BENDER) script verilator > $@

synth/vivado.f: Bender.lock Bender.yml
	$(BENDER) script vivado > $@

lint: verilator.f
	$(VERILATOR) -lint-only -f verilator.f --top $(TOP)

synth: synth/vivado.f $(SRCS) synth/build.tcl synth/dummy_constraints.xdc
	./synth/run.sh $(VIVADO_SETTINGS) $(VIVADO) $(TOP)

clean:
	rm -f *.f
	rm -f synth/*.f
	rm -f synth/run.tcl
	rm -rf synth/.Xil
	rm -f synth/*.log synth/*.jou
