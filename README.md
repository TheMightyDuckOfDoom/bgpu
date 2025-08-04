# BGPU: A Bad GPU

<div align="center">

[![Lint RTL](https://github.com/TheMightyDuckOfDoom/bgpu/actions/workflows/lint.yml/badge.svg)](https://github.com/TheMightyDuckOfDoom/bgpu/actions/workflows/lint.yml)
[![Simulation](https://github.com/TheMightyDuckOfDoom/bgpu/actions/workflows/sim.yml/badge.svg)](https://github.com/TheMightyDuckOfDoom/bgpu/actions/workflows/sim.yml)
[![Xilinx Simulation](https://github.com/TheMightyDuckOfDoom/bgpu/actions/workflows/sim_xilinx.yml/badge.svg)](https://github.com/TheMightyDuckOfDoom/bgpu/actions/workflows/sim_xilinx.yml)
[![Gowin Simulation](https://github.com/TheMightyDuckOfDoom/bgpu/actions/workflows/sim_gowin.yml/badge.svg)](https://github.com/TheMightyDuckOfDoom/bgpu/actions/workflows/sim_gowin.yml)
[![ASIC Synthesis](https://github.com/TheMightyDuckOfDoom/bgpu/actions/workflows/synth_asic.yml/badge.svg)](https://github.com/TheMightyDuckOfDoom/bgpu/actions/workflows/synth_asic.yml)
[![Xilinx Synthesis](https://github.com/TheMightyDuckOfDoom/bgpu/actions/workflows/synth_xilinx.yml/badge.svg)](https://github.com/TheMightyDuckOfDoom/bgpu/actions/workflows/synth_xilinx.yml)
[![Gowin Synthesis](https://github.com/TheMightyDuckOfDoom/bgpu/actions/workflows/synth_gowin.yml/badge.svg)](https://github.com/TheMightyDuckOfDoom/bgpu/actions/workflows/synth_gowin.yml)
[![License](https://img.shields.io/badge/license-SHL--0.51-green)](LICENSE-SHL)
</div>

## Project Goals

1. **Educational**: Main purpose of BGPU is to get a better understanding of GPGPU architectures, their design decisions and tradeoffs.

2. **Highly Configurable**: For design-space-exploration purposes most things should be parameterizable. Sample configurations / optimal rations of different parameters should be explored and documented.

3. **Open-Source**: BGPU should run with open-source tools (simulator, assembler/compiler, synthesis/implementation).

3. **FPGA Implementation**: BGPU should be able to run on reasonably sized FPGAs with acceptable performance.

## Architecture

The Architecture of BGPU is most similar to NVIDIA GPUs starting from the Fermi-Microarchitecture.
We implement a form of Independent-Thread-Scheduling (ITS) similiar to the NVIDIA Volta Architecture.

TODO: As with all projects, documentation is still a work-in-progress...

## Helpfull References

Books:
- "General-Purpose Graphics Processor Architecture" by Tor M. Aamodt, Wilson Wai Lun Fung and Timothy G. Rogers

Articles / Papers:
- "NVIDIA TESLA: A Unified Graphics and Computing Architecture" by Erik Lindholm, John Nickolls, Stuart Oberman and John Montrym

Websites:
- GPGPU-Sim Wiki: http://gpgpu-sim.org/manual/index.php

Introduction to GPU Roofline Performance Model
- "Basic facts about GPUs": https://damek.github.io/random/basic-facts-about-gpus/

## License
All code in this repository should have a permissive license. Hardware is licensed under Solderpad Hardware License 0.51 (see [`LICENSE-SHL`](LICENSE-SHL))

## Copyright

© Tobias Senti 2025
