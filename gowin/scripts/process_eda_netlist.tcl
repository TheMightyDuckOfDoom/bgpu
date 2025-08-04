# Renames modules/ports/signals in an EDA netlist to be compatible with Verilator for post-synthesis simulation.
yosys read_verilog gowin/out/${top_design}/impl/gwsynthesis/${top_design}.vg
yosys hierarchy -top ${top_design}
yosys write_json gowin/out/${top_design}.json
exec python3 gowin/scripts/rename_ports.py gowin/out/${top_design}.json $top_design
yosys design -reset
yosys read_json gowin/out/${top_design}.json
yosys write_verilog gowin/out/post_synth.v
