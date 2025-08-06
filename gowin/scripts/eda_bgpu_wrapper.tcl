exec mkdir -p gowin/out

# B has no SSRAMs
set device GW5AST-LV138PG484AC1/I0
set device_version B

set top_design "bgpu_soc"

create_project -name ${top_design} -dir gowin/out/ -pn ${device} -device_version ${device_version} -force

set_option -top_module "bgpu_wrapper"
set_option -disable_io_insertion 1
set_option -verilog_std sysv2017

add_file ../pickled.sv
add_file ../../src/dummy_constraints.sdc
add_file ../../src/pll/pll_init.v
add_file ../../src/pll/gowin_pll_50m_to_40m.v
add_file ../../src/pll/gowin_pll_50m_to_40m_mod.v
add_file ../../src/bgpu_wrapper.sv
run syn

# Check for synthesis errors
source ../../scripts/eda_check_warnings.tcl
