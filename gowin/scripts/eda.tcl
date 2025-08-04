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
set error 0
proc check_for_warning {warning_as_error} {
    global top_design
    global error

    set fp [open impl/gwsynthesis/${top_design}.log]
    set filecontent [read $fp]
    set input_list [split $filecontent "\n"]
    set textlist [lsearch -all -inline $input_list "*${warning_as_error}*"]
    set error 0
    foreach elem $textlist {
        puts $elem
        set error 1
    }
    close $fp
}

check_for_warning "DI0002"
check_for_warning "EX0200"
check_for_warning "EX0201"
check_for_warning "EX0205"
check_for_warning "EX0206"
check_for_warning "EX0210"

if {$error} {
    puts "Error: Warnings that should be errors found in synthesis log, aborting."
    exit 2
}
