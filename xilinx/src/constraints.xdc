# Clocks in MHz
set CLK_SYS 200

set SYS_CLK_PERIOD  [expr 1000.0 / $CLK_SYS]

create_clock -add -name clk_sys  -period $SYS_CLK_PERIOD  [get_ports {sys_clk_p}];

# System clock
set_property VCCAUX_IO   DONTCARE    [get_ports {sys_clk_p}]
set_property IOSTANDARD  DIFF_SSTL15 [get_ports {sys_clk_p}]
set_property PACKAGE_PIN AB11        [get_ports {sys_clk_p}]

set_property VCCAUX_IO   DONTCARE    [get_ports {sys_clk_n}]
set_property IOSTANDARD  DIFF_SSTL15 [get_ports {sys_clk_n}]
set_property PACKAGE_PIN AC11        [get_ports {sys_clk_n}]

# System Reset
set_property -dict { PACKAGE_PIN AC16 IOSTANDARD LVCMOS15 } [get_ports {sys_rst_ni}]

# LEDs
set_property -dict { PACKAGE_PIN AA2  IOSTANDARD LVCMOS15 } [get_ports {led[0]}]
set_property -dict { PACKAGE_PIN AD5  IOSTANDARD LVCMOS15 } [get_ports {led[1]}]
set_property -dict { PACKAGE_PIN W10  IOSTANDARD LVCMOS15 } [get_ports {led[2]}]
set_property -dict { PACKAGE_PIN Y10  IOSTANDARD LVCMOS15 } [get_ports {led[3]}]
set_property -dict { PACKAGE_PIN AE10 IOSTANDARD LVCMOS15 } [get_ports {led[4]}]
set_property -dict { PACKAGE_PIN W11  IOSTANDARD LVCMOS15 } [get_ports {led[5]}]
set_property -dict { PACKAGE_PIN V11  IOSTANDARD LVCMOS15 } [get_ports {led[6]}]
set_property -dict { PACKAGE_PIN Y12  IOSTANDARD LVCMOS15 } [get_ports {led[7]}]

# Bitsream
set_property BITSTREAM.GENERAL.COMPRESS     TRUE    [current_design]
set_property BITSTREAM.CONFIG.CCLK_TRISTATE TRUE    [current_design]
set_property BITSTREAM.CONFIG.CONFIGRATE     66     [current_design]
set_property CONFIG_VOLTAGE                  2.5    [current_design]
set_property CFGBVS                          VCCO   [current_design]
set_property BITSTREAM.CONFIG.SPI_32BIT_ADDR YES    [current_design]
set_property BITSTREAM.CONFIG.SPI_BUSWIDTH   4      [current_design]
set_property BITSTREAM.CONFIG.SPI_FALL_EDGE  YES    [current_design]
set_property BITSTREAM.CONFIG.UNUSEDPIN      PULLUP [current_design]
