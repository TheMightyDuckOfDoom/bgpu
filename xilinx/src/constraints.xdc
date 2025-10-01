# Clocks in MHz
set CLK_SYS_200 200
set CLK_SYS_100 100
set CLK_JTAG 50

set SYS_CLK_200_PERIOD [expr 1000.0 / $CLK_SYS_200]
set SYS_CLK_100_PERIOD [expr 1000.0 / $CLK_SYS_100]
set JTAG_CLK_PERIOD    [expr 1000.0 / $CLK_JTAG]

# 1066.6 DDR3 / 8 = 133 MHz
set SOC_CLK_PERIOD 7.5

create_clock -add -name clk_sys_200 -period $SYS_CLK_200_PERIOD [get_ports {sys_clk_200_pi}]
create_clock -add -name clk_sys_100 -period $SYS_CLK_100_PERIOD [get_ports {sys_clk_100_i}]
create_clock -add -name clk_jtag    -period $JTAG_CLK_PERIOD    [get_pins {i_bgpu/i_ctrl_domain/i_dmi_jtag/i_dmi_jtag_tap/i_tap_dtmcs/TCK}]

# System clock
set_property VCCAUX_IO   DONTCARE    [get_ports {sys_clk_200_pi}]
set_property IOSTANDARD  DIFF_SSTL15 [get_ports {sys_clk_200_pi}]
set_property PACKAGE_PIN AB11        [get_ports {sys_clk_200_pi}]

set_property VCCAUX_IO   DONTCARE    [get_ports {sys_clk_200_ni}]
set_property IOSTANDARD  DIFF_SSTL15 [get_ports {sys_clk_200_ni}]
set_property PACKAGE_PIN AC11        [get_ports {sys_clk_200_ni}]

set_property VCCAUX_IO   DONTCARE [get_ports {sys_clk_100_i}]
set_property IOSTANDARD  LVCMOS33 [get_ports {sys_clk_100_i}]
set_property PACKAGE_PIN F17      [get_ports {sys_clk_100_i}]

# Clock Groups
set_clock_groups -asynchronous -group [get_clocks {clk_jtag}] -group [get_clocks {clk_pll_i}] -group [get_clocks {clk_sys_100}]

# System Reset
set_input_delay -max [expr $SYS_CLK_200_PERIOD * 0.1] -clock clk_sys_200 [get_ports {sys_rst_ni}]
set_false_path -hold                            -from                    [get_ports {sys_rst_ni}]
set_max_delay [expr $SYS_CLK_200_PERIOD * 0.75] -from                    [get_ports {sys_rst_ni}]

set_property -dict { PACKAGE_PIN AC16 IOSTANDARD LVCMOS15 } [get_ports {sys_rst_ni}]

# LEDs
set_max_delay 50.0   -to [get_ports {led_o[*]}]
set_false_path -hold -to [get_ports {led_o[*]}]

set_property -dict { PACKAGE_PIN AA2  IOSTANDARD LVCMOS15 } [get_ports {led_o[0]}]
set_property -dict { PACKAGE_PIN AD5  IOSTANDARD LVCMOS15 } [get_ports {led_o[1]}]
set_property -dict { PACKAGE_PIN W10  IOSTANDARD LVCMOS15 } [get_ports {led_o[2]}]
set_property -dict { PACKAGE_PIN Y10  IOSTANDARD LVCMOS15 } [get_ports {led_o[3]}]
set_property -dict { PACKAGE_PIN AE10 IOSTANDARD LVCMOS15 } [get_ports {led_o[4]}]
set_property -dict { PACKAGE_PIN W11  IOSTANDARD LVCMOS15 } [get_ports {led_o[5]}]
set_property -dict { PACKAGE_PIN V11  IOSTANDARD LVCMOS15 } [get_ports {led_o[6]}]
set_property -dict { PACKAGE_PIN Y12  IOSTANDARD LVCMOS15 } [get_ports {led_o[7]}]

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
set_max_delay [expr $SOC_CLK_PERIOD * 0.5] -through [get_nets {i_bgpu/i_ctrl_domain/i_dmi_jtag/i_dmi_cdc/i_cdc_req/async_*}]
set_max_delay [expr $SOC_CLK_PERIOD * 0.5] -through [get_nets {i_bgpu/i_ctrl_domain/i_dmi_jtag/i_dmi_cdc/i_cdc_resp/async_*}]

# Management CPU
set_max_delay [expr $SOC_CLK_PERIOD * 0.5] -through [get_nets {i_bgpu/i_ctrl_domain/i_mgmt_cpu_wrapper/i_cdc_dmem_a/async_*}]
set_max_delay [expr $SOC_CLK_PERIOD * 0.5] -through [get_nets {i_bgpu/i_ctrl_domain/i_mgmt_cpu_wrapper/i_cdc_dmem_r/async_*}]
set_max_delay [expr $SOC_CLK_PERIOD * 0.5] -through [get_nets {i_bgpu/i_ctrl_domain/i_mgmt_cpu_wrapper/i_cdc_imem_a/async_*}]
set_max_delay [expr $SOC_CLK_PERIOD * 0.5] -through [get_nets {i_bgpu/i_ctrl_domain/i_mgmt_cpu_wrapper/i_cdc_imem_r/async_*}]
