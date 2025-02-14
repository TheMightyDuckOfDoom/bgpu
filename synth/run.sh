#!/bin/bash
source $1
cd synth
echo -n 'set top "' > run.tcl
echo -n $3 >> run.tcl
echo '"' >> run.tcl
echo 'set device "xc7k325tffg676-2l"' >> run.tcl
echo "source build.tcl" >> run.tcl
echo "source run.tcl" | $2 vivado -mode tcl | tee /tmp/log
