#!/bin/bash
# Copyright 2025 Tobias Senti
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

NumWarps_range=(1 2 4 8 16)
WaitBufferSizePerWarp_range=(1 2 4 8)

for NumWarp in ${NumWarps_range[@]}
do
    for WaitBufferSizePerWarp in ${WaitBufferSizePerWarp_range[@]}
    do
        InflightInstructionsPerWarp=$((2 * WaitBufferSizePerWarp))
        TblocksToLaunch=$((NumWarp * WaitBufferSizePerWarp + 1))
        result=$(make tb_compute_unit VERILATOR_ARGS="-GNumWarps=$NumWarp -GWaitBufferSizePerWarp=$WaitBufferSizePerWarp -GInflightInstrPerWarp=$InflightInstructionsPerWarp -GTblocksToLaunch=$TblocksToLaunch -GMaxSimCycles=2000")
        if [ $? -eq 0 ]; then
            echo "Simulation passed for NumWarp: $NumWarp, WaitBufferSizePerWarp: $WaitBufferSizePerWarp InflightInstructionsPerWarp: $InflightInstructionsPerWarp TblocksToLaunch: $TblocksToLaunch"
            echo "$result" | grep -A1 "All thread blocks done."
        else
            echo "$result" > failure.log
            cat failure.log
            echo "Simulation failed for NumWarp: $NumWarp, WaitBufferSizePerWarp: $WaitBufferSizePerWarp InflightInstructionsPerWarp: $InflightInstructionsPerWarp TblocksToLaunch: $TblocksToLaunch"
            exit 1
        fi
    done
    echo ""
done

echo "All simulations passed"
