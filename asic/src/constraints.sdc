create_clock -add -name sys_clk_pin -period 1 -waveform {0 0.5} [get_ports {clk_i}];
set_input_delay  -clock sys_clk_pin 0 [all_inputs]
set_output_delay -clock sys_clk_pin 0 [all_outputs]
