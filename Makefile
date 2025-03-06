# Tobias Senti, Feb-March 2025

# Source files
SRCS = $(wildcard src/*.sv)
TB_SRCS = $(wildcard test/*.sv)

# Tools
BENDER          ?= bender
VERILATOR       ?= verilator
VIVADO          ?= vivado
VIVADO_SETTINGS ?= /tools/Xilinx/Vivado/202?.?/settings64.sh

TOP ?= compute_unit
TB_TOP ?= tb_$(TOP)

@PHONY: lint synth clean

# Targets
verilator.f: Bender.lock Bender.yml
	$(BENDER) script verilator > $@

verilator_tb.f: Bender.lock Bender.yml
	$(BENDER) script verilator -t sim > $@

synth/vivado.f: Bender.lock Bender.yml
	$(BENDER) script vivado > $@

lint: verilator.f
	$(VERILATOR) -lint-only -f verilator.f --top $(TOP)

sim: verilator_tb.f $(SRCS) $(TB_SRCS)
	$(VERILATOR) -f verilator_tb.f --top $(TB_TOP) --binary -j 0 --timing --Wno-fatal --trace --trace-structs
	make -C obj_dir -j -f V$(TB_TOP).mk V$(TB_TOP)
	./obj_dir/V$(TB_TOP)

synth: synth/vivado.f $(SRCS) synth/build.tcl synth/dummy_constraints.xdc
	time ./synth/run.sh $(VIVADO_SETTINGS) $(VIVADO) $(TOP)

clean:
	rm -f *.f
	rm -rf obj_dir
	rm -f synth/*.f
	rm -f synth/run.tcl
	rm -rf synth/.Xil
	rm -f synth/*.log synth/*.jou
