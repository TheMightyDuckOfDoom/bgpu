# Makes timing closure harder
set power_opt 0

set_param general.maxThreads 8
set_part $device
# read all design files
source vivado_impl.f
add_files -norecurse -fileset [current_fileset] [list \
    $ROOT/xilinx/src/bgpu_wrapper.sv \
]

# Set Defines for board
set upper_board [string toupper $board]
set defines [get_property verilog_define [current_fileset]]
lappend defines BOARD
lappend defines BOARD_${upper_board}
set_property verilog_define $defines [current_fileset]

# read ip
read_ip $ROOT/xilinx/out/ip/memory_controller/memory_controller.xci

# read constraints
read_xdc src/boards/${board}.xdc
read_xdc src/constraints.xdc

# Synthesize Design
puts $top
puts $device
synth_design -top $top -part $device -verbose -debug_log

# Report helper function
exec mkdir -p $ROOT/xilinx/out/reports/
exec mkdir -p $ROOT/xilinx/out/checkpoints
exec mkdir -p $ROOT/xilinx/out/netlists
exec rm -rf $ROOT/xilinx/out/reports/$top
exec mkdir -p $ROOT/xilinx/out/reports/$top
proc make_reports {prefix} {
    global ROOT
    global top
    report_power -file $ROOT/xilinx/out/reports/$top/${prefix}_power.rpt
    report_timing -nworst 1 -file $ROOT/xilinx/out/reports/$top/${prefix}_timing_max.rpt
    report_timing_summary -file $ROOT/xilinx/out/reports/$top/${prefix}_timing_sum.rpt
    report_utilization -hierarchical -hierarchical_percentages -file $ROOT/xilinx/out/reports/$top/${prefix}_util.rpt
}

# Synthesis Reports
make_reports 1_synth
# write_verilog -force -mode funcsim out/netlists/${top}_1_synth.v
write_checkpoint -force out/checkpoints/${top}_1_synth.dcp

# Optimize Design (Integrating IPs)
opt_design -verbose
make_reports 2_opt
# write_verilog -force -mode funcsim out/netlists/${top}_2_opt.v
write_checkpoint -force out/checkpoints/${top}_2_opt.dcp

# Optional Power Optimization
if {$power_opt} {
    power_opt_design -verbose
    report_power_opt -file $ROOT/xilinx/out/reports/$top/3_power_opt_power_opt.rpt
    make_reports 3_power_opt
}

# Place the design
place_design -verbose -directive Explore
make_reports 4_place
# write_verilog -force -mode funcsim out/netlists/${top}_4_place.v
write_checkpoint -force out/checkpoints/${top}_4_place.dcp

# Physical Optimization looping
set_clock_uncertainty -setup 0.2 [get_clocks clk_pll_i]
set opt_loops 5
set loop_num 1
while {1} {
    phys_opt_design -directive AggressiveExplore -verbose
    report_phys_opt -file $ROOT/xilinx/out/reports/$top/5_phys_opt_phys_opt_${loop_num}_1.rpt
    set wns [get_property SLACK [get_timing_paths]]
    if {$wns >= 0} {
        break
    }
    phys_opt_design -directive AggressiveFanoutOpt
    report_phys_opt -file $ROOT/xilinx/out/reports/$top/5_phys_opt_phys_opt_${loop_num}_2.rpt
    set wns [get_property SLACK [get_timing_paths]]
    if {$wns >= 0} {
        break
    }
    phys_opt_design -directive AlternateReplication
    report_phys_opt -file $ROOT/xilinx/out/reports/$top/5_phys_opt_phys_opt_${loop_num}_3.rpt
    set wns [get_property SLACK [get_timing_paths]]
    if {$wns >= 0} {
        break
    }
    if {$loop_num >= $opt_loops} {
        puts "WARNING: Failed to meet timing after ${opt_loops} phys_opt loops, WNS=${wns}"
        break
    }
    set loop_num [expr $loop_num + 1]
}
set_clock_uncertainty -setup 0 [get_clocks clk_pll_i]
make_reports 5_phys_opt
# write_verilog -force -mode funcsim out/netlists/${top}_5_phys_opt.v
write_checkpoint -force out/checkpoints/${top}_5_phys_opt.dcp

# Another round of optional Power Optimizations
if {$power_opt} {
    power_opt_design -verbose
    report_power_opt -file $ROOT/xilinx/out/reports/$top/6_postplace_power_opt_power_opt.rpt
    make_reports 6_postplace_power_opt
}

# Route the design
route_design -directive AggressiveExplore
make_reports 7_route
# write_verilog -force -mode funcsim out/netlists/${top}_7_route.v
write_checkpoint -force out/checkpoints/${top}_7_route.dcp

# Final Physical Optimizations
phys_opt_design -directive AggressiveExplore -verbose
report_phys_opt -file $ROOT/xilinx/out/reports/$top/8_phys_opt_phys_opt.rpt
make_reports 8_phys_opt
# write_verilog -force -mode funcsim out/netlists/${top}_8_phys_opt.v

# Write checkpoint
write_checkpoint -force out/checkpoints/${top}_8_phys_opt.dcp

# Write out bitfile
write_bitstream -force out/${top}.bit
