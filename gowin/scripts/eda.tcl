exec mkdir -p gowin/out

# B has no SSRAMs
set device GW5AST-LV138PG484AC1/I0
set device_version B

create_project -name ${top_design} -dir gowin/out/ -pn ${device} -device_version ${device_version} -force

set_option -top_module $top_design
set_option -verilog_std sysv2017
set_option -replicate_resources 1
set_option -place_option 3
if { $top_design != "bgpu_soc" } {
    set_option -disable_io_insertion 1
} else {
    add_file ../../src/bgpu_wrapper.sv
    set_option -top_module bgpu_wrapper
    set_option -use_jtag_as_gpio 1
}

add_file ../pickled.sv
add_file -type sdc ../../src/constraints.sdc
add_file -type cst ../../src/tangmega.cst
run syn

if { $top_design == "bgpu_soc"} {
    run pnr
}
