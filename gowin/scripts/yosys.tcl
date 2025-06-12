yosys -import
plugin -i slang.so
yosys read_slang --top $top_design -F gowin/gowin-yosys.f \
        --compat-mode --keep-hierarchy \
        --allow-use-before-declare --ignore-unknown-modules

exec mkdir -p gowin/out

#nowidelut: better results
#nolutram: 138k B does not support SSRAMs/LUTRAMs
synth_gowin -top $top_design -noiopads -nowidelut -nolutram

write_verilog -simple-lhs -decimal -attr2comment -renameprefix gen gowin/out/$top_design.v
