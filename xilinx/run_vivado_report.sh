#!/bin/bash

source $1
cd xilinx
sed 's/,/,\n/g' out/${3}_yosys.v > out/${3}_yosys_commabreak.v
echo -n 'set top "' > run_vivado_report.tcl
echo -n $3 >> run_vivado_report.tcl
echo '"' >> run_vivado_report.tcl
echo 'set device "xc7k325tffg676-2"' >> run_vivado_report.tcl
# echo 'set device "xc7v2000tflg1925-1"' >> run_vivado_report.tcl
# echo 'set device "xcku060-ffva1156-1-c"' >> run_vivado_report.tcl
# echo 'set device "xcku13p-ffve900-1-i"' >> run_vivado_report.tcl
echo "source scripts/vivado_report.tcl" >> run_vivado_report.tcl
echo "source run_vivado_report.tcl" | $2 vivado -mode tcl

num_errors=$(grep -c ERROR vivado.log)

# If we have more than 1 error, we should fail the build
# First error is:
# ERROR: [Coretcl 2-1982] Project file does not exist. Please provide a project file with .xpr extension. Provided: vivado
if [ $num_errors -gt 1 ]; then
    echo "\nERROR: Vivado failed"
    grep ERROR vivado.log
    exit 1
fi

period=$(grep create_clock dummy_constraints.xdc | awk '{print $6}')
slack=$(grep slack vivado.log | tail -n1 | awk '{print $2}')
python3 -c "print(f'Max frequency: {1000/(${period}-(${slack})):.2f} MHz')"
