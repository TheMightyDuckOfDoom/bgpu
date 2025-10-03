#!/bin/bash
source $1
cd xilinx
echo -n 'set top "' > run_vivado.tcl
echo -n $3 >> run_vivado.tcl
echo '"' >> run_vivado.tcl
echo -n 'set board ' >> run_vivado.tcl
echo $5 >> run_vivado.tcl
echo "source scripts/boards.tcl" >> run_vivado.tcl
echo -n "source scripts/" >> run_vivado.tcl
echo $4 >> run_vivado.tcl
echo "source run_vivado.tcl" | LD_PRELOAD=/lib/x86_64-linux-gnu/libudev.so.1 $2 vivado -mode tcl

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
