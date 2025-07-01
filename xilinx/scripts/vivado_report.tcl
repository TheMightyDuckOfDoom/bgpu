set_param general.maxThreads 8

read_verilog out/${top}_yosys_commabreak.v
link_design -top $top -part $device

read_xdc dummy_constraints.xdc

report_timing -nworst 1
report_utilization -hierarchical -hierarchical_percentages
