
set SYS_CLK_200_PERIOD  [expr 1000.0 / $CLK_SYS_200]
set SYS_CLK_MGMT_PERIOD [expr 1000.0 / $CLK_MGMT]
set JTAG_CLK_PERIOD     [expr 1000.0 / $CLK_JTAG]

create_clock -add -name clk_sys_200 -period $SYS_CLK_200_PERIOD [get_ports {sys_clk_200_pi}]
create_clock -add -name clk_mgmt    -period $SYS_CLK_MGMT_PERIOD [get_ports {mgmt_clk_i}]
create_clock -add -name clk_jtag    -period $JTAG_CLK_PERIOD    [get_pins {i_bgpu/i_ctrl_domain/i_dmi_jtag/i_dmi_jtag_tap/i_tap_dtmcs/TCK}]

# Clock Groups
set_clock_groups -asynchronous -group [get_clocks {clk_jtag}] -group [get_clocks {clk_pll_i}] -group [get_clocks {clk_mgmt}]

# System Reset
set_input_delay -max [expr $SYS_CLK_200_PERIOD * 0.1] -clock clk_sys_200 [get_ports {sys_rst_ni}]
set_false_path -hold                            -from                    [get_ports {sys_rst_ni}]
set_max_delay [expr $SYS_CLK_200_PERIOD * 0.75] -from                    [get_ports {sys_rst_ni}]

# LEDs
set_max_delay 50.0   -to [get_ports {led_o[*]}]
set_false_path -hold -to [get_ports {led_o[*]}]

### Clock Domain Crossings

# Constrain `cdc_2phase` for DMI request
set_max_delay [expr $SOC_CLK_PERIOD * 0.5] -through [get_nets {i_bgpu/i_ctrl_domain/i_dmi_jtag/i_dmi_cdc/i_cdc_req/async_*}]
set_max_delay [expr $SOC_CLK_PERIOD * 0.5] -through [get_nets {i_bgpu/i_ctrl_domain/i_dmi_jtag/i_dmi_cdc/i_cdc_resp/async_*}]

# Management CPU
set_max_delay [expr $SOC_CLK_PERIOD * 0.5] -through [get_nets {i_bgpu/i_ctrl_domain/i_mgmt_cpu_wrapper/i_cdc_dmem_a/async_*}]
set_max_delay [expr $SOC_CLK_PERIOD * 0.5] -through [get_nets {i_bgpu/i_ctrl_domain/i_mgmt_cpu_wrapper/i_cdc_dmem_r/async_*}]
set_max_delay [expr $SOC_CLK_PERIOD * 0.5] -through [get_nets {i_bgpu/i_ctrl_domain/i_mgmt_cpu_wrapper/i_cdc_imem_a/async_*}]
set_max_delay [expr $SOC_CLK_PERIOD * 0.5] -through [get_nets {i_bgpu/i_ctrl_domain/i_mgmt_cpu_wrapper/i_cdc_imem_r/async_*}]
