# Copyright (c) 2022 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Authors:
# - Philippe Sauter <phsauter@iis.ee.ethz.ch>

# Tools
YOSYS    ?= yosys

# Directories
# directory of the path to the last called Makefile (this one)
YOSYS_DIR 		:= $(realpath $(dir $(realpath $(lastword $(MAKEFILE_LIST)))))
YOSYS_OUT		:= $(YOSYS_DIR)/out
YOSYS_TMP		:= $(YOSYS_DIR)/tmp
YOSYS_REPORTS	:= $(YOSYS_DIR)/reports

# top level to be synthesized
TOP       		?= compute_unit
# target period in picoseconds
PERIOD_PS		?= 10000

# file containing include dirs, defines and paths to all source files
SV_FLIST    	:= asic/yosys.f

# path to the resulting netlists (debug preserves multibit signals)
NETLIST			:= $(YOSYS_OUT)/$(TOP)_yosys.v
NETLIST_DEBUG	:= $(YOSYS_OUT)/$(TOP)_debug_yosys.v

## Synthesize netlist using Yosys
asic: $(NETLIST)

$(NETLIST) $(NETLIST_DEBUG):  $(SV_FLIST)
	@mkdir -p $(YOSYS_OUT)
	@mkdir -p $(YOSYS_TMP)
	@mkdir -p $(YOSYS_REPORTS)
	cd $(YOSYS_DIR) && \
	SV_FLIST="yosys.f" \
	TOP_DESIGN="$(TOP)" \
	PERIOD_PS="$(PERIOD_PS)" \
	TMP="$(YOSYS_TMP)" \
	OUT="$(YOSYS_OUT)" \
	REPORTS="$(YOSYS_REPORTS)" \
	$(YOSYS) -c $(YOSYS_DIR)/scripts/yosys_synthesis.tcl \
		2>&1 | TZ=UTC gawk '{ print strftime("[%Y-%m-%d %H:%M %Z]"), $$0 }' \
		     | tee "$(YOSYS_DIR)/$(TOP).log" \
		     | gawk -f $(YOSYS_DIR)/scripts/filter_output.awk;

asic-report:
	tail -n 128 $(YOSYS_REPORTS)/$(TOP)_area.rpt

asic-clean:
	rm -rf $(YOSYS_OUT)
	rm -rf $(YOSYS_TMP)
	rm -rf $(YOSYS_REPORTS) 
	rm -f $(YOSYS_DIR)/*.log
	rm -rf $(SV_FLIST)

.PHONY: asic-clean asic asic-report
