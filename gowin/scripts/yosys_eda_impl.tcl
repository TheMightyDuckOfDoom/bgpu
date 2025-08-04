exec mkdir -p gowin/out

# B has no SSRAMs
set device GW5AST-LV138PG484AC1/I0
set device_version B
set top_design bgpu_soc

create_project -name ${top_design}_yosys -dir gowin/out/ -pn ${device} -device_version ${device_version} -force

set_option -top_module bgpu_wrapper
set_option -verilog_std sysv2017
set_option -use_jtag_as_gpio 1

add_file ../${top_design}_yosys.v
add_file ../../src/gowin_pll_50_to_30/pll_init.v
add_file ../../src/gowin_pll_50_to_30/gowin_pll_mod.v
add_file ../../src/gowin_pll_50_to_30/gowin_pll.v
add_file ../../src/bgpu_wrapper.sv
add_file -type sdc ../../src/constraints.sdc
add_file ../../src/tangmega.cst
run syn
run pnr
