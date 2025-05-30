# BGPU: A Bad GPU

<div align="center">

[![Lint RTL](https://github.com/TheMightyDuckOfDoom/bgpu/actions/workflows/lint.yml/badge.svg)](https://github.com/TheMightyDuckOfDoom/bgpu/actions/workflows/lint.yml)
[![Simulate](https://github.com/TheMightyDuckOfDoom/bgpu/actions/workflows/sim.yml/badge.svg)](https://github.com/TheMightyDuckOfDoom/bgpu/actions/workflows/sim.yml)
[![License](https://img.shields.io/badge/license-SHL--0.51-green)](LICENSE-SHL)
</div>

## Project Goals

1. **Educational**: Main purpose of BGPU is to get a better understanding of GPGPU architectures, their design decisions and tradeoffs.

2. **Highly Configurable**: For design-space-exploration purposes most things should be parameterizable. Sample configurations / optimal rations of different parameters should be explored and documented.

3. **Open-Source**: BGPU should run with open-source tools (simulator, assembler/compiler, synthesis/implementation).

3. **FPGA Implementation**: BGPU should be able to run on a reasonably sized FPGAs with acceptable performance.

## Architecture

The Architecture of BGPU has similarities with NVIDIA GPUs starting from the Fermi-Microarchitecture.

TODO: As with all projects, documentation is still a work-in-progress...

## Helpfull References

Books:
- "General-Purpose Graphics Processor Architecture" by Tor M. Aamodt, Wilson Wai Lun Fung and Timothy G. Rogers

Articles / Papers:
- "NVIDIA TESLA: A Unified Graphics and Computing Architecture" by Erik Lindholm, John Nickolls, Stuart Oberman and John Montrym

Websites:
- GPGPU-Sim Wiki: http://gpgpu-sim.org/manual/index.php

## License
All code in this repository should have a permissive license. Hardware is licensed under Solderpad Hardware License 0.51 (see [`LICENSE-SHL`](LICENSE-SHL))

## Copyright

© Tobias Senti 2025