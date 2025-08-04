open_project gowin/out/$top_design/$top_design.gprj

# We use jtag pins for the debug module
set_option -use_jtag_as_gpio 1

# Add proper timing and pin constraints
catch {add_file ../../src/constraints.sdc} error
catch {add_file ../../src/tang_mega_138k.cst} error

# Disable dummy constraints
catch {set_file_enable ../../src/dummy_constraints.sdc false} error
catch {set_file_enable ../../src/constraints.sdc true} error

# Run Placement and Routing
run pnr
