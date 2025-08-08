### External Clocks

# 50 MHz External Clock
create_clock -name clk_ext -period 20.0 [get_ports {clk_i}]

# 20 MHz External JTAG Clock
create_clock -name clk_jtg -period 50.0 [get_ports {jtag_tck_i}]

### PLL Generated Clocks

# 160 MHz Memory Clock to DDR3 controller -> clk_ext * 16 / 2
create_generated_clock -name clk_mem -source [get_ports {clk_i}] -master_clock clk_ext -divide_by 5 -multiply_by 16 -duty_cycle 50 [get_nets {clk_memory}]

# 50 MHz System Clock -> clk_ext
create_generated_clock -name clk50 -source [get_ports {clk_i}] -master_clock clk_ext -duty_cycle 50 [get_nets {clk50}]

### Additional Generated Clocks

# 100 Mhz Memory Controller Clock -> clk_mem / 4
create_generated_clock -name clk_sys -source [get_nets {clk_memory}] -master_clock clk_mem -divide_by 4 -duty_cycle 50 [get_nets {clk_sys}]

#### Clock Groups

set_clock_groups -asynchronous -group [get_clocks {clk_jtg}] -group [get_clocks {clk_sys}] -group [get_clocks {clk_ext}] -group [get_clocks {clk_mem}] -group [get_clocks {clk50}]

#### Input/Output Delays

# Reset should propagate within a clock cycle.
set_input_delay -max 2.0 -clock clk_sys [get_nets {rst_ni}]
set_false_path -hold -from [get_nets {rst_ni}]
set_max_delay 15.0   -from [get_nets {rst_ni}]

# JTAG Reset should propagate within a clock cycle.
set_input_delay -max 5.0 -clock clk_jtg [get_ports {jtag_trst_ni}]  
set_false_path -hold -from [get_ports {jtag_trst_ni}]
set_max_delay 45.0   -from [get_ports {jtag_trst_ni}]

# JTAG signals
set_input_delay  -min -add_delay -clock clk_jtg 5.0  [get_ports {jtag_tdi_i jtag_tms_i}]
set_input_delay  -max -add_delay -clock clk_jtg 25.0 [get_ports {jtag_tdi_i jtag_tms_i}]
set_output_delay -min -add_delay -clock clk_jtg 2.5  [get_ports {jtag_tdo_o}]
set_output_delay -max -add_delay -clock clk_jtg 12.5 [get_ports {jtag_tdo_o}]

#### Clock Domain Crossing (CDC)

# Constrain `cdc_2phase` for DMI request
set_false_path -hold -through [get_nets {i_bgpu/i_ctrl_domain/i_dmi_jtag/i_dmi_cdc/i_cdc_req/async_*}]
set_max_delay 7.0    -through [get_nets {i_bgpu/i_ctrl_domain/i_dmi_jtag/i_dmi_cdc/i_cdc_req/async_*}]

# Constrain `cdc_2phase` for DMI response
set_false_path -hold -through [get_nets {i_bgpu/i_ctrl_domain/i_dmi_jtag/i_dmi_cdc/i_cdc_resp/async_*}]
set_max_delay 7.0    -through [get_nets {i_bgpu/i_ctrl_domain/i_dmi_jtag/i_dmi_cdc/i_cdc_resp/async_*}]
