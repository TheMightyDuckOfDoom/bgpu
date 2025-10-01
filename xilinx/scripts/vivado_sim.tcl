set_param general.maxThreads 8
exec mkdir -p out
exec rm -rf $top

create_project -force -part $device $top out/$top

source vivado_sim.f

set_property top $top [get_fileset sim_1]

launch_simulation 
run all
