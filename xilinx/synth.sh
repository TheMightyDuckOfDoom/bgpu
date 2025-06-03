#!/bin/bash
source $1
cd xilinx
echo -n 'set top "' > run_synth.tcl
echo -n $3 >> run_synth.tcl
echo '"' >> run_synth.tcl
echo 'set device "xc7k325tffg676-2l"' >> run_synth.tcl
echo "source synth.tcl" >> run_synth.tcl
echo "source run_synth.tcl" | $2 vivado -mode tcl

num_errors=$(grep -c ERROR vivado.log)

# If we have more than 1 error, we should fail the build
# First error is:
# ERROR: [Coretcl 2-1982] Project file does not exist. Please provide a project file with .xpr extension. Provided: vivado
if [ $num_errors -gt 1 ]; then
    echo "\nERROR: Vivado failed"
    grep ERROR vivado.log
    exit 1
fi
