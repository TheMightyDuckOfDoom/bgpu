yosys read_verilog gowin/out/${TOP}_yosys/impl/gwsynthesis/${TOP}_yosys.vg
yosys hierarchy -top ${TOP}
yosys write_json gowin/out/${TOP}_yosys.json
exec python3 gowin/scripts/rename_ports.py gowin/out/${TOP}_yosys.json $WRAPPER
yosys design -reset
yosys read_json gowin/out/${TOP}_yosys.json
yosys write_verilog gowin/out/post_synth.v
