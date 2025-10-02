yosys -import
plugin -i slang.so
yosys read_slang --top $top_design -F xilinx/yosys.f \
        --compat-mode --keep-hierarchy \
        --allow-use-before-declare --ignore-unknown-modules

exec mkdir -p xilinx/out

synth_xilinx -top $top_design -family xc7 -noclkbuf -nolutram -noiopad -abc9 -flatten -run :coarse

# Needed to avoid later crash, see:
# - https://github.com/YosysHQ/yosys/issues/4349
# - https://github.com/YosysHQ/yosys/issues/4451
splitnets -format __v
stat -tech xilinx
yosys rename -wire -suffix _reg t:*dff*
select -write xilinx/out/${top_design}_registers.rpt t:*dff*
# rename all other cells
autoname t:*dff* %n
clean -purge

synth_xilinx -top $top_design -family xc7 -noclkbuf -noiopad -nolutram -abc9 -flatten -run coarse:

# Work around Verilator V3String bug when hashing long names
yosys rename -scramble-name -seed 42

write_verilog -simple-lhs -attr2comment -renameprefix gen xilinx/out/${top_design}_yosys.v
stat -tech xilinx
