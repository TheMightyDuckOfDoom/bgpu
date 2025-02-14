# Tobias Senti, Feb 2025

# Source files
SRCS = $(wildcard src/*.sv)

# Tools
BENDER          ?= bender
VERILATOR       ?= verilator
VIVADO          ?= vivado
VIVADO_SETTINGS ?= /tools/Xilinx/Vivado/202?.?/settings64.sh

TOP ?= fetcher

@PHONY: lint synth clean

# Targets
verilator.f: Bender.lock Bender.yml
	$(BENDER) script verilator > $@

vivado.f: Bender.lock Bender.yml
	$(BENDER) script vivado > $@

lint: verilator.f
	$(VERILATOR) -lint-only -f verilator.f --top $(TOP)

synth: vivado.f $(SRCS)
	./synth/run.sh $(VIVADO_SETTINGS) $(VIVADO) $(TOP)

clean:
	rm -f *.f
	rm -f synth/run.tcl
	rm -rf synth/.Xil
	rm -f synth/*.log synth/*.jou
