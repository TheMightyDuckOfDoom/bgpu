# create_clock -add -name sys_clk_pin -period 5 -waveform {0 2.5} [get_ports {clk_i}];
create_clock -add -name sys_clk_pin -period 4 -waveform {0 2} [get_ports {clk_i}];
set_input_delay  -clock sys_clk_pin 0 [all_inputs]
set_output_delay -clock sys_clk_pin 0 [all_outputs]
