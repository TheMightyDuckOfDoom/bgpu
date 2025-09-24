#!/bin/bash
source $1
cd xilinx
echo -n 'set top "' > run_vivado.tcl
echo -n $3 >> run_vivado.tcl
echo '"' >> run_vivado.tcl
echo 'set device "xc7k325tffg676-2l"' >> run_vivado.tcl
# echo 'set device "xc7v2000tflg1925-1"' >> run_vivado.tcl
# echo 'set device "xcku060-ffva1156-1-c"' >> run_vivado.tcl
# echo 'set device "xcku13p-ffve900-1-i"' >> run_vivado.tcl
echo -n "source scripts/" >> run_vivado.tcl
echo $4 >> run_vivado.tcl
echo "source run_vivado.tcl" | $2 vivado -mode tcl

num_errors=$(grep -c ERROR vivado.log)

# If we have more than 1 error, we should fail the build
# First error is:
# ERROR: [Coretcl 2-1982] Project file does not exist. Please provide a project file with .xpr extension. Provided: vivado
if [ $num_errors -gt 1 ]; then
    echo "\nERROR: Vivado failed"
    grep ERROR vivado.log
    exit 1
fi

if [ $4 == "vivado.tcl" ]; then
    period=$(grep create_clock dummy_constraints.xdc | awk '{print $6}')
    slack=$(grep slack vivado.log | tail -n1 | awk '{print $2}')
    python3 -c "print(f'Max frequency: {1000/(${period}-(${slack})):.2f} MHz')"
fi
