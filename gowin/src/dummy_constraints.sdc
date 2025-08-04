create_clock -name clk_sys -period 5.0 [get_ports {clk_i}]
set_input_delay  -clock clk_sys 0 [all_inputs]
set_output_delay -clock clk_sys 0 [all_outputs]
