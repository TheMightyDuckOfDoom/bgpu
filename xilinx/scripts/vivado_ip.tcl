set_param general.maxThreads 8

create_project -in_memory -part $device
exec mkdir -p out/ip/

create_ip -name mig_7series -vendor xilinx.com -library ip -module_name memory_controller -dir out/ip/ -force

exec cp src/ip/mig_ddr3_1066_1GB.prj out/ip/memory_controller/
set_property -dict [list \
                    CONFIG.XML_INPUT_FILE {mig_ddr3_1066_1GB.prj}] [get_ips]

generate_target all [get_ips]

synth_ip [get_ips]
