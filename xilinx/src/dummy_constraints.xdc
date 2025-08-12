# Clocks in MHz
set CLK_SYS 200
set CLK_MGMT_CPU 100

set SYS_CLK_PERIOD  [expr 1000.0 / $CLK_SYS]
set MGMT_CLK_PERIOD [expr 1000.0 / $CLK_MGMT_CPU]

create_clock -add -name clk_sys  -period $SYS_CLK_PERIOD  [get_ports {clk_i}];
create_clock -add -name clk_mgmt -period $MGMT_CLK_PERIOD [get_ports {mgmt_cpu_clk_i}];

set_input_delay  -clock clk_sys 0 [all_inputs ]
set_output_delay -clock clk_sys 0 [all_outputs]
