set_thread_count 8

source scripts/openroad_init_tech.tcl

set TOP compute_unit

read_verilog out/${TOP}_yosys.v
link_design $TOP

read_sdc src/constraints.sdc
report_checks
