set_param general.maxThreads 8
set_part $device

# read all design files
source vivado.f

# read constraints
read_xdc dummy_constraints.xdc

# Synthesize Design
puts $top
puts $device
synth_design -top $top -part $device -verbose -debug_log -mode out_of_context
#-flatten_hierarchy none
report_power
report_timing -nworst 1
report_utilization -hierarchical -hierarchical_percentages
# report_timing_summary
# Opt Design
# opt_design
# report_utilization -hierarchical -hierarchical_percentages
# report_timing_summary
# Place Design
place_design -verbose 

phys_opt_design -directive AddRetime
# Route Design
# route_design -verbose -timing_summary
# report_timing_summary
report_timing -nworst 1
report_utilization -hierarchical -hierarchical_percentages

#start_gui

# exec mkdir -p out
# write_verilog -force -mode funcsim out/$top.v

# Write out bitfile
## write_bitstream -force my_proj.bit
