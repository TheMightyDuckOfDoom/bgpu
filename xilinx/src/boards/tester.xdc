# This is just a dummy XDC file for the XC7V2000T Tester Board
# It currently does not represent the actual board

# Clocks in MHz
set CLK_SYS_200 200
set CLK_MGMT 100
set CLK_JTAG 50

# 800 DDR2 / 8 = 100 MHz
set SOC_CLK_PERIOD 10

# System clocks
set_property VCCAUX_IO   DONTCARE      [get_ports {sys_clk_200_pi}]
set_property IOSTANDARD  DIFF_SSTL18_I [get_ports {sys_clk_200_pi}]
set_property PACKAGE_PIN AH27          [get_ports {sys_clk_200_pi}]

set_property VCCAUX_IO   DONTCARE      [get_ports {sys_clk_200_ni}]
set_property IOSTANDARD  DIFF_SSTL18_I [get_ports {sys_clk_200_ni}]
set_property PACKAGE_PIN AH28          [get_ports {sys_clk_200_ni}]

set_property VCCAUX_IO   DONTCARE [get_ports {mgmt_clk_i}]
set_property IOSTANDARD  LVCMOS18 [get_ports {mgmt_clk_i}]
set_property PACKAGE_PIN AA28     [get_ports {mgmt_clk_i}]

# Reset button
set_property -dict { PACKAGE_PIN R28 IOSTANDARD LVCMOS18 } [get_ports {sys_rst_ni}]

# LEDs
set_property -dict { PACKAGE_PIN P30 IOSTANDARD LVCMOS18 } [get_ports {led_o[0]}]
set_property -dict { PACKAGE_PIN M30 IOSTANDARD LVCMOS18 } [get_ports {led_o[1]}]
set_property -dict { PACKAGE_PIN N30 IOSTANDARD LVCMOS18 } [get_ports {led_o[2]}]

# SLRs: Distribute Compute Clusters across SLRs
# set_property USER_SLR_ASSIGNMENT SLR0 [get_cells {i_bgpu/gen_compute_clusters[0].i_cc}]
# set_property USER_SLR_ASSIGNMENT SLR0 [get_cells {i_bgpu/gen_compute_clusters[4].i_cc}]

# set_property USER_SLR_ASSIGNMENT SLR1 [get_cells {i_bgpu/gen_compute_clusters[1].i_cc}]
# set_property USER_SLR_ASSIGNMENT SLR1 [get_cells {i_bgpu/gen_compute_clusters[5].i_cc}]

# set_property USER_SLR_ASSIGNMENT SLR2 [get_cells {i_bgpu/gen_compute_clusters[2].i_cc}]
# set_property USER_SLR_ASSIGNMENT SLR2 [get_cells {i_bgpu/gen_compute_clusters[6].i_cc}]

# set_property USER_SLR_ASSIGNMENT SLR3 [get_cells {i_bgpu/gen_compute_clusters[3].i_cc}]
# set_property USER_SLR_ASSIGNMENT SLR3 [get_cells {i_bgpu/gen_compute_clusters[7].i_cc}]
