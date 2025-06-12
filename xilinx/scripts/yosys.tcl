yosys -import
plugin -i slang.so
yosys read_slang --top $top_design -F xilinx/yosys.f \
        --compat-mode --keep-hierarchy \
        --allow-use-before-declare --ignore-unknown-modules

exec mkdir -p xilinx/out

#synth_gowin -top $top_design -noiopads -nowidelut -nolutram
synth_xilinx -top $top_design -family xc7 -noiopad -nowidelut -flatten -abc9 -edif xilinx/out/$top_design.edif

write_verilog -simple-lhs -decimal -attr2comment -renameprefix gen xilinx/out/${top_design}_yosys.v
stat -tech xilinx
