set_part $device

# read all design files
source vivado.f

# read constraints
read_xdc dummy_constraints.xdc

# Synthesize Design
puts $top
puts $device
synth_design -top $top -part $device -verbose -debug_log
#-flatten_hierarchy none
report_power
report_timing -nworst 1
report_utilization -hierarchical -hierarchical_percentages
#report_timing_summary
# Opt Design
#opt_design
# Place Design
#place_design
# Route Design
#route_design
#report_timing -nworst 1
#report_utilization -hierarchical

#start_gui

# Write out bitfile
## write_bitstream -force my_proj.bit
