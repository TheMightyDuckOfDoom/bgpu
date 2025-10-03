set_param general.maxThreads 8

create_project -in_memory -part $device
exec mkdir -p out/ip/

exec rm -rf out/ip/memory_controller
create_ip -name mig_7series -vendor xilinx.com -library ip -module_name memory_controller -dir out/ip/ -force

exec cp src/ip/${mig_cfg}.prj out/ip/memory_controller/mig.prj
set_property -dict [list \
                    CONFIG.XML_INPUT_FILE {mig.prj}] [get_ips]

generate_target all [get_ips]

synth_ip [get_ips]
