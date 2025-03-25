# Tobias Senti, Feb-March 2025

# Source files
SRCS = $(wildcard src/*.sv)
TB_SRCS = $(wildcard test/*.sv)

# Tools
BENDER          ?= bender
VERILATOR       ?= verilator
VIVADO          ?= vivado
VIVADO_SETTINGS ?= /tools/Xilinx/Vivado/202?.?/settings64.sh
VERIBLE_LINT    ?= verible-verilog-lint

VERILATOR_FLAGS:= verilator/config.vlt

BENDER_DEPS:= Bender.lock Bender.yml

TOP ?= compute_unit
TB_TOP ?= tb_$(TOP)

@PHONY: lint synth clean

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
	$(BENDER) script verilator -t sim > $@

# Translate RTL to C++ using Verilator
verilator/obj_dir/V%.mk: verilator/verilator_tb.f verilator/config.vlt $(SRCS) $(TB_SRCS)
	$(VERILATOR) $(VERILATOR_FLAGS) -f $< --top $* --binary -j 0 --timing --assert --trace --trace-structs --Mdir verilator/obj_dir

# Build the testbench
verilator/obj_dir/V%: verilator/obj_dir/V%.mk
	make -C verilator/obj_dir -j -f V$*.mk V$*

# Run the testbench
tb_%: verilator/obj_dir/Vtb_%
	./$<

####################################################################################################
# Synthesis
####################################################################################################

# Generate filelist for Vivado synthesis
synth/vivado.f: $(BENDER_DEPS)
	$(BENDER) script vivado > $@

# Run Vivado synthesis
synth: synth/vivado.f $(SRCS) synth/build.tcl synth/dummy_constraints.xdc synth/run.sh
	time ./synth/run.sh $(VIVADO_SETTINGS) $(VIVADO) $(TOP)

####################################################################################################
# Clean
####################################################################################################

clean:
	rm -f verilator/*.f
	rm -rf verilator/obj_dir
	rm -f synth/*.f
	rm -f synth/run.tcl
	rm -rf synth/.Xil
	rm -f synth/*.log synth/*.jou
