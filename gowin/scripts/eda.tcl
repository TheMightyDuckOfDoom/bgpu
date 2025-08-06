exec mkdir -p gowin/out

# B has no SSRAMs
set device GW5AST-LV138PG484AC1/I0
set device_version B

create_project -name ${top_design} -dir gowin/out/ -pn ${device} -device_version ${device_version} -force

set_option -top_module $top_design
set_option -disable_io_insertion 1
set_option -verilog_std sysv2017

add_file ../pickled.sv
add_file ../../src/dummy_constraints.sdc
run syn

# Check for synthesis errors
source ../../scripts/eda_check_warnings.tcl
