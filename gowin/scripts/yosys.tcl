yosys -import
plugin -i slang.so
yosys read_slang --top $top_design -F gowin/gowin-yosys.f \
        --compat-mode --keep-hierarchy \
        --allow-use-before-declare --ignore-unknown-modules

exec mkdir -p gowin/out

yosys setattr -set keep_hierarchy 1 "t:dmi_jtag$*"
yosys setattr -set keep_hierarchy 1 "t:cdc_*$*"
yosys setattr -set keep_hierarchy 1 "t:sync$*"
yosys setattr -set keep_hierarchy 1 "t:tc_clk*$*"

yosys attrmap -rename dont_touch keep
yosys attrmvcp -copy -attr keep

#nolutram: 138k B does not support SSRAMs/LUTRAMs
synth_gowin -top $top_design -noiopads -nolutram -run :coarse

# Needed to avoid later crash, see:
# - https://github.com/YosysHQ/yosys/issues/4349
# - https://github.com/YosysHQ/yosys/issues/4451
splitnets -format __v
yosys rename -wire -suffix _reg t:*dff*
select -write gowin/out/${top_design}_registers.rpt t:*dff*
# rename all other cells
autoname t:*dff* %n
clean -purge

synth_gowin -top $top_design -noiopads -nolutram -run coarse:

write_verilog -simple-lhs -attr2comment -renameprefix gen gowin/out/${top_design}_yosys.v
