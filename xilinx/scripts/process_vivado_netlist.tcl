# Renames modules/ports/signals in an Vivado netlist to be compatible with Verilator for post-synthesis simulation.
yosys read_verilog -Dglbl xilinx/out/${top_design}_vivado.v
yosys hierarchy -top ${top_design}
yosys write_json xilinx/out/${top_design}.json

# Modify netlist
exec python3 xilinx/scripts/rename_ports.py xilinx/out/${top_design}.json $top_design

# Read in modified netlist
yosys design -reset
yosys read_json xilinx/out/${top_design}.json

# Work around Verilator V3String bug when hashing long names
yosys rename -scramble-name -seed 42

yosys write_verilog xilinx/out/post_synth.v
