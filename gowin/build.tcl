yosys -import
plugin -i slang.so
yosys read_slang --top $top_design -F gowin/gowin.f \
        --compat-mode --keep-hierarchy \
        --allow-use-before-declare --ignore-unknown-modules

exec mkdir -p gowin/out

synth_gowin -top $top_design -nowidelut -noalu -vout gowin/out/$top_design.v
