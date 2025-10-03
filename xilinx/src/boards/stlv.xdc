# Clocks in MHz
set CLK_SYS_200 200
set CLK_MGMT 100
set CLK_JTAG 50

# 1066.6 DDR3 / 8 = 133 MHz
set SOC_CLK_PERIOD 7.5

# System clocks
set_property VCCAUX_IO   DONTCARE    [get_ports {sys_clk_200_pi}]
set_property IOSTANDARD  DIFF_SSTL15 [get_ports {sys_clk_200_pi}]
set_property PACKAGE_PIN AB11        [get_ports {sys_clk_200_pi}]

set_property VCCAUX_IO   DONTCARE    [get_ports {sys_clk_200_ni}]
set_property IOSTANDARD  DIFF_SSTL15 [get_ports {sys_clk_200_ni}]
set_property PACKAGE_PIN AC11        [get_ports {sys_clk_200_ni}]

set_property VCCAUX_IO   DONTCARE [get_ports {mgmt_clk_i}]
set_property IOSTANDARD  LVCMOS33 [get_ports {mgmt_clk_i}]
set_property PACKAGE_PIN F17      [get_ports {mgmt_clk_i}]

# Reset button
set_property -dict { PACKAGE_PIN AC16 IOSTANDARD LVCMOS15 } [get_ports {sys_rst_ni}]

# LEDs
set_property -dict { PACKAGE_PIN AA2  IOSTANDARD LVCMOS15 } [get_ports {led_o[0]}]
set_property -dict { PACKAGE_PIN AD5  IOSTANDARD LVCMOS15 } [get_ports {led_o[1]}]
set_property -dict { PACKAGE_PIN W10  IOSTANDARD LVCMOS15 } [get_ports {led_o[2]}]

# Bitstream
set_property BITSTREAM.GENERAL.COMPRESS      TRUE   [current_design]
set_property BITSTREAM.CONFIG.CCLK_TRISTATE  TRUE   [current_design]
set_property BITSTREAM.CONFIG.CONFIGRATE     66     [current_design]
set_property CONFIG_VOLTAGE                  2.5    [current_design]
set_property CFGBVS                          VCCO   [current_design]
set_property BITSTREAM.CONFIG.SPI_32BIT_ADDR YES    [current_design]
set_property BITSTREAM.CONFIG.SPI_BUSWIDTH   4      [current_design]
set_property BITSTREAM.CONFIG.SPI_FALL_EDGE  YES    [current_design]
set_property BITSTREAM.CONFIG.UNUSEDPIN      PULLUP [current_design]
