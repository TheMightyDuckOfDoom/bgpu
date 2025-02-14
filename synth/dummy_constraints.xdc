create_clock -add -name sys_clk_pin -period 10 -waveform {0 5} [get_ports {clk_i}];
