#!/bin/bash
source $1
cd xilinx
echo -n 'set top "' > run.tcl
echo -n $3 >> run.tcl
echo '"' >> run.tcl
echo 'set device "xc7k325tffg676-2l"' >> run.tcl
echo "source build.tcl" >> run.tcl
echo "source run.tcl" | $2 vivado -mode tcl

num_errors=$(grep -c ERROR vivado.log)

# If we have more than 1 error, we should fail the build
# First error is:
# ERROR: [Coretcl 2-1982] Project file does not exist. Please provide a project file with .xpr extension. Provided: vivado
if [ $num_errors -gt 1 ]; then
    echo "\nERROR: Vivado failed"
    grep ERROR vivado.log
    exit 1
fi
