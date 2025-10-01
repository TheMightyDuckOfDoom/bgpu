# Clocks in MHz
set CLK_SYS 200
set CLK_JTAG 50

set SYS_CLK_PERIOD  [expr 1000.0 / $CLK_SYS]
set JTAG_CLK_PERIOD [expr 1000.0 / $CLK_JTAG]

# 1066.6 DDR3 / 8 = 133 MHz
set SOC_CLK_PERIOD 7.5

create_clock -add -name clk_sys  -period $SYS_CLK_PERIOD  [get_ports {sys_clk_p}]
create_clock -add -name clk_jtag -period $JTAG_CLK_PERIOD [get_pins {i_bgpu/i_ctrl_domain/i_dmi_jtag/i_dmi_jtag_tap/i_tap_dtmcs/TCK}]

# System clock
set_property VCCAUX_IO   DONTCARE    [get_ports {sys_clk_p}]
set_property IOSTANDARD  DIFF_SSTL15 [get_ports {sys_clk_p}]
set_property PACKAGE_PIN AB11        [get_ports {sys_clk_p}]

set_property VCCAUX_IO   DONTCARE    [get_ports {sys_clk_n}]
set_property IOSTANDARD  DIFF_SSTL15 [get_ports {sys_clk_n}]
set_property PACKAGE_PIN AC11        [get_ports {sys_clk_n}]

# Clock Groups
set_clock_groups -asynchronous -group [get_clocks {clk_jtag}] -group [get_clocks {clk_pll_i}]

# System Reset
set_input_delay -max [expr $SYS_CLK_PERIOD * 0.1] -clock clk_sys [get_ports {sys_rst_ni}]
set_false_path -hold                        -from                [get_ports {sys_rst_ni}]
set_max_delay [expr $SYS_CLK_PERIOD * 0.75] -from                [get_ports {sys_rst_ni}]

set_property -dict { PACKAGE_PIN AC16 IOSTANDARD LVCMOS15 } [get_ports {sys_rst_ni}]

# LEDs
set_max_delay 50.0   -to [get_ports {led[*]}]
set_false_path -hold -to [get_ports {led[*]}]

set_property -dict { PACKAGE_PIN AA2  IOSTANDARD LVCMOS15 } [get_ports {led[0]}]
set_property -dict { PACKAGE_PIN AD5  IOSTANDARD LVCMOS15 } [get_ports {led[1]}]
set_property -dict { PACKAGE_PIN W10  IOSTANDARD LVCMOS15 } [get_ports {led[2]}]
set_property -dict { PACKAGE_PIN Y10  IOSTANDARD LVCMOS15 } [get_ports {led[3]}]
set_property -dict { PACKAGE_PIN AE10 IOSTANDARD LVCMOS15 } [get_ports {led[4]}]
set_property -dict { PACKAGE_PIN W11  IOSTANDARD LVCMOS15 } [get_ports {led[5]}]
set_property -dict { PACKAGE_PIN V11  IOSTANDARD LVCMOS15 } [get_ports {led[6]}]
set_property -dict { PACKAGE_PIN Y12  IOSTANDARD LVCMOS15 } [get_ports {led[7]}]

# Bitsream
set_property BITSTREAM.GENERAL.COMPRESS      TRUE   [current_design]
set_property BITSTREAM.CONFIG.CCLK_TRISTATE  TRUE   [current_design]
set_property BITSTREAM.CONFIG.CONFIGRATE     66     [current_design]
set_property CONFIG_VOLTAGE                  2.5    [current_design]
set_property CFGBVS                          VCCO   [current_design]
set_property BITSTREAM.CONFIG.SPI_32BIT_ADDR YES    [current_design]
set_property BITSTREAM.CONFIG.SPI_BUSWIDTH   4      [current_design]
set_property BITSTREAM.CONFIG.SPI_FALL_EDGE  YES    [current_design]
set_property BITSTREAM.CONFIG.UNUSEDPIN      PULLUP [current_design]

### Clock Domain Crossings

# Constrain `cdc_2phase` for DMI request
set_false_path -hold -through [get_nets {i_bgpu/i_ctrl_domain/i_dmi_jtag/i_dmi_cdc/i_cdc_req/async_*}]
set_max_delay [expr $SOC_CLK_PERIOD * 0.5] -through [get_nets {i_bgpu/i_ctrl_domain/i_dmi_jtag/i_dmi_cdc/i_cdc_req/async_*}]

# Constrain `cdc_2phase` for DMI response
set_false_path -hold -through [get_nets {i_bgpu/i_ctrl_domain/i_dmi_jtag/i_dmi_cdc/i_cdc_resp/async_*}]
set_max_delay [expr $SOC_CLK_PERIOD * 0.5] -through [get_nets {i_bgpu/i_ctrl_domain/i_dmi_jtag/i_dmi_cdc/i_cdc_resp/async_*}]
