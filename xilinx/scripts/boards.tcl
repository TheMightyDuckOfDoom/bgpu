# Set up board-specific parameters

if {$board == "ypcb"} { # ypcb_00338_1p1
    set mig_cfg ypcb_mig_0_2GB
    set device  xc7k480tffg1156-2
} elseif {$board == "stlv"} { # stlv7325
    set mig_cfg stlv_mig_ddr3_1066_1GB
    set device  xc7k325tffg676-2
} elseif {$board == "tester"} { # xc7v2000t_tester
    set mig_cfg tester_ddr2_800
    set device  xc7v2000tflg1925-1
}

# echo 'set device "xc7v2000tflg1925-1"' >> run_vivado.tcl
# echo 'set device "xcku060-ffva1156-1-c"' >> run_vivado.tcl
# echo 'set device "xcku13p-ffve900-1-i"' >> run_vivado.tcl
