# Makes timing closure harder
set power_opt 0

set_param general.maxThreads 8
set_part $device

# read all design files
source vivado_impl.f
add_files -norecurse -fileset [current_fileset] [list \
    $ROOT/xilinx/src/bgpu_wrapper.sv \
]

# read constraints
read_xdc src/constraints.xdc

# read ip
read_ip $ROOT/xilinx/out/ip/memory_controller/memory_controller.xci

# Synthesize Design
puts $top
puts $device
synth_design -top $top -part $device -verbose -debug_log

exec mkdir -p $ROOT/xilinx/out/reports/
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

make_reports 1_synth

opt_design -verbose
make_reports 2_opt

if {$power_opt} {
    power_opt_design -verbose
    report_power_opt -file $ROOT/xilinx/out/reports/$top/3_power_opt_power_opt.rpt
    make_reports 3_power_opt
}

place_design -verbose 
make_reports 4_place

phys_opt_design -directive AddRetime -verbose
report_phys_opt -file $ROOT/xilinx/out/reports/$top/5_phys_opt_phys_opt.rpt
make_reports 5_phys_opt

if {$power_opt} {
    power_opt_design -verbose
    report_power_opt -file $ROOT/xilinx/out/reports/$top/6_postplace_power_opt_power_opt.rpt
    make_reports 6_postplace_power_opt
}

route_design
make_reports 7_route

phys_opt_design -directive AggressiveExplore -verbose
report_phys_opt -file $ROOT/xilinx/out/reports/$top/8_phys_opt_phys_opt.rpt
make_reports 8_phys_opt

# Write checkpoint
write_checkpoint -force out/final.dcp

# Write out bitfile
write_bitstream -force out/bgpu.bit
