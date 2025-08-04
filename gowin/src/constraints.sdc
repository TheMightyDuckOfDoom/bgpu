create_clock -name clk_sys -period 20.0 [get_ports {clk_i}]
create_clock -name clk_jtg -period 50.0 [get_ports {jtag_tck_i}]
create_clock -name clk_jtg_n -period 50.0 [get_nets {i_ctrl_domain/i_dmi_jtag/i_dmi_jtag_tap/tck_n}]

set_clock_groups -asynchronous -group [get_clocks {clk_jtg clk_jtg_n}] -group [get_clocks {clk_sys}]

# Reset should propagate to system domain within a clock cycle.
set_input_delay -max 2.0 -clock clk_sys [get_nets {rst_ni}]
set_false_path -hold -from [get_nets {rst_ni}]
set_max_delay 15.0   -from [get_nets {rst_ni}]

set_input_delay -max 2.0 -clock clk_sys [get_nets {testmode_i}]
set_false_path -hold -from [get_nets {testmode_i}]
set_max_delay 15.0   -from [get_nets {testmode_i}]

# Constrain `cdc_2phase` for DMI request
set_false_path -hold -through [get_nets {i_ctrl_domain/i_dmi_jtag/i_dmi_cdc/i_cdc_req/async_*}]
set_max_delay 7.0    -through [get_nets {i_ctrl_domain/i_dmi_jtag/i_dmi_cdc/i_cdc_req/async_*}]

# Constrain `cdc_2phase` for DMI response
set_false_path -hold -through [get_nets {i_ctrl_domain/i_dmi_jtag/i_dmi_cdc/i_cdc_resp/async_*}]
set_max_delay 7.0    -through [get_nets {i_ctrl_domain/i_dmi_jtag/i_dmi_cdc/i_cdc_resp/async_*}]

set_input_delay  -min -add_delay -clock clk_jtg 5.0  [get_ports {jtag_tdi_i jtag_tms_i}]
set_input_delay  -max -add_delay -clock clk_jtg 25.0 [get_ports {jtag_tdi_i jtag_tms_i}]
set_output_delay -min -add_delay -clock clk_jtg 2.5  [get_ports {jtag_tdo_o}]
set_output_delay -max -add_delay -clock clk_jtg 12.5 [get_ports {jtag_tdo_o}]

# Reset should propagate to system domain within a clock cycle.
set_input_delay -max 5.0 -clock clk_jtg [get_ports {jtag_trst_ni}]  
set_false_path -hold -from [get_ports {jtag_trst_ni}]
set_max_delay 45.0   -from [get_ports {jtag_trst_ni}]
