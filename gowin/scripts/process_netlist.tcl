yosys read_verilog gowin/out/$TOP/impl/gwsynthesis/$TOP.vg
yosys write_json gowin/out/$TOP.json
exec python3 gowin/scripts/rename_ports.py gowin/out/$TOP.json $TOP
yosys design -reset
yosys read_json gowin/out/$TOP.json
yosys write_verilog gowin/out/post_synth.v
