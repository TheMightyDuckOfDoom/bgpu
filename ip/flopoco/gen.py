#!/usr/bin/env python3
# From https://github.com/jiegec/fpu-wrappers/blob/master/fpu-wrappers/resources/flopoco/gen.py

import subprocess
import os

tasks = [
# {
#     'type': 'H',
#     'exp': 5,
#     'frac': 10
# },
{
    'type': 'S',
    'exp': 8,
    'frac': 23
},
# {
#     'type': 'D',
#     'exp': 11,
#     'frac': 52
# }
]

flopoco = 'flopoco'
flopoco_411 = flopoco + '-4.1.1'

def gen_fma(frequency, task):
    # generate vhdl
    command = [flopoco, "allRegistersWithAsyncReset=1", "IEEEFPFMA", f"wE={task['exp']}", f"wF={task['frac']}",
               f"name=IEEEFMA_{task['type']}", f"frequency={frequency}"]
    print(' '.join(command))
    out = subprocess.check_output(
        command,
        stderr=subprocess.STDOUT).decode('utf-8')

    print(out)

    # parse stages from output
    stages = out.splitlines()[-1]
    print(stages)
    stages = stages.split(',')[0].split('c')[1]

    # save vhdl
    name = f"IEEEFMA_{task['type']}{stages}"
    file = f"{name}.vhdl"
    os.rename('flopoco.vhdl', file)

    # synthesize to verilog
    os.system("mkdir -p IEEEFMA")
    os.system(f"yosys -m ghdl -p 'ghdl --std=08 -fsynopsys -fexplicit {name}.vhdl -e IEEEFMA_{task['type']}; hierarchy -top IEEEFMA_{task['type']}; rename -top {name}; write_verilog IEEEFMA/{name}.v'")

def gen_fix2fp(frequency, task):
    # generate vhdl
    command = [flopoco_411, "Fix2FP", f"wE={task['exp']}", f"wF={task['frac']}",
               "LSB=0", f"MSB={task['exp']+task['frac']}",
               f"name=Fix2FP_{task['type']}", f"frequency={frequency}"]
    print(' '.join(command))
    out = subprocess.check_output(
        command,
        stderr=subprocess.STDOUT).decode('utf-8')

    print(out)

    # parse stages from output
    stages = 0
    for line in out.splitlines():
        if 'Pipeline depth' in line:
            stages = int(line.split(' ')[-1])

    # save vhdl
    name = f"Fix2FP_{task['type']}{stages}"
    file = f"{name}.vhdl"
    os.rename('flopoco.vhdl', file)

    # synthesize to verilog
    os.system("mkdir -p Fix2FP")
    os.system(f"yosys -m ghdl -p 'ghdl --std=08 -fsynopsys -fexplicit {name}.vhdl -e Fix2FP_{task['type']}; hierarchy -top Fix2FP_{task['type']}; rename -top {name}; write_verilog Fix2FP/{name}.v'")

def gen_fp2fix(frequency, task):
    # generate vhdl
    command = [flopoco, "allRegistersWithAsyncReset=1", "FP2Fix", f"wE={task['exp']}", f"wF={task['frac']}",
               "LSB=0", f"MSB={task['exp']+task['frac']}",
               f"name=FP2Fix_{task['type']}", f"frequency={frequency}"]
    print(' '.join(command))
    out = subprocess.check_output(
        command,
        stderr=subprocess.STDOUT).decode('utf-8')

    print(out)

    # parse stages from output
    stages = out.splitlines()[-1]
    print(stages)
    stages = stages.split(',')[0].split('c')[1]

    # save vhdl
    name = f"FP2Fix_{task['type']}{stages}"
    file = f"{name}.vhdl"
    os.rename('flopoco.vhdl', file)

    # synthesize to verilog
    os.system("mkdir -p FP2Fix")
    os.system(f"yosys -m ghdl -p 'ghdl --std=08 -fsynopsys -fexplicit {name}.vhdl -e FP2Fix_{task['type']}; hierarchy -top FP2Fix_{task['type']}; rename -top {name}; write_verilog FP2Fix/{name}.v'")

def gen_IEEE2fp(frequency, task):
    # generate vhdl
    command = [flopoco, "allRegistersWithAsyncReset=1", "InputIEEE", f"wEIn={task['exp']}", f"wFIn={task['frac']}",
               f"wEOut={task['exp']}", f"wFOut={task['frac']}",
               f"name=IEEE2FP_{task['type']}", f"frequency={frequency}"]
    print(' '.join(command))
    out = subprocess.check_output(
        command,
        stderr=subprocess.STDOUT).decode('utf-8')

    print(out)

    # parse stages from output
    stages = out.splitlines()[-1]
    print(stages)
    stages = stages.split(',')[0].split('c')[1]

    # save vhdl
    name = f"IEEE2FP_{task['type']}{stages}"
    file = f"{name}.vhdl"
    os.rename('flopoco.vhdl', file)

    # synthesize to verilog
    os.system("mkdir -p IEEE2FP")
    os.system(f"yosys -m ghdl -p 'ghdl --std=08 -fsynopsys -fexplicit {name}.vhdl -e IEEE2FP_{task['type']}; hierarchy -top IEEE2FP_{task['type']}; rename -top {name}; write_verilog IEEE2FP/{name}.v'")

def gen_fp2IEEEp(frequency, task):
    # generate vhdl
    command = [flopoco, "allRegistersWithAsyncReset=1", "OutputIEEE", f"wEIn={task['exp']}", f"wFIn={task['frac']}",
               f"wEOut={task['exp']}", f"wFOut={task['frac']}",
               f"name=FP2IEEE_{task['type']}", f"frequency={frequency}"]
    print(' '.join(command))
    out = subprocess.check_output(
        command,
        stderr=subprocess.STDOUT).decode('utf-8')

    print(out)

    # parse stages from output
    stages = out.splitlines()[-1]
    print(stages)
    stages = stages.split(',')[0].split('c')[1]

    # save vhdl
    name = f"FP2IEEE_{task['type']}{stages}"
    file = f"{name}.vhdl"
    os.rename('flopoco.vhdl', file)

    # synthesize to verilog
    os.system("mkdir -p FP2IEEE")
    os.system(f"yosys -m ghdl -p 'ghdl --std=08 -fsynopsys -fexplicit {name}.vhdl -e FP2IEEE_{task['type']}; hierarchy -top FP2IEEE_{task['type']}; rename -top {name}; write_verilog FP2IEEE/{name}.v'")


os.system("rm -rf IEEEFMA")
os.system("rm -rf Fix2FP")
os.system("rm -rf FP2Fix")
os.system("rm -rf IEEE2FP")
os.system("rm -rf FP2IEEE")
for task in tasks:
    for frequency in [100, 150, 200, 250, 300, 400]:
        gen_fma(frequency, task)
        gen_fix2fp(frequency, task)
        gen_fp2fix(frequency, task)
        gen_IEEE2fp(frequency, task)
        gen_fp2IEEEp(frequency, task)

    os.system("rm -f *.vhdl")
