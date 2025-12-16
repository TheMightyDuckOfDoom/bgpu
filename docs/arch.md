# BGPU: A Bad GPU

## BGPU SoC

This is the top most module in the BGPU-Architecture.
It currently contains the following:
- Control Domain: Allowing JTAG access and launching of kernels
- One or more Compute Clusters
- Various AXI-Interconnects to connect the Control Domain and Compute Clusters to a Memory Controller

## Control Domain

The Control Domain allows us to control the Compute Clusters.

It contains the following modules:
- RISC-V JTAG Debug Module
- RISC-V RV32I Processor
- Thread Engine
- AXI and OBI Interconnects

## Compute Clusters

A Compute Cluster is composed out of one or more Compute Units.

## Compute Unit

The Compute Unit is the heart of the BGPU.
This is the place where we actually do usefull computations (hopefully).

The following diagram gives an overview of the Compute Unit:

<img src="fig/compute_unit.drawio.svg">

An instruction flows through these stages:
- Fetcher: Selects a PC of a Warp that should fetch new instructions
- Instruction Cache: Retrieves one or more (if FetchWidth > 1) instructions at the PC
- Decoder: Decodes the instructions. Tell the fetcher where the next PC will be for the Warp
- Multi Warp Dispatcher: Keeps Instructions in an Wait Buffer until they are allowed to be executed. Dispatches one or more (if DispatchWidth > 1) to collect their operands
- Register Operand Collector Stage: Read the Operands of the Instructions
- Execution Unit Demultiplexer: Sends the Instructions to their respective Execution Unit
- Branch Unit: Calculates the PC for Conditional Branches
- Integer Unit: Performs integer operations and housekeeping operations (index within threadblock, get parameter address, ...)
- Floating Point Unit: Performs Floating Point operations
- Load Store Unit: Performs Loads and Stores to/from Memory
- Result Collector: Arbitrates between Execution Unit Results and sends them to the Register File
