#!/bin/bash
# Copyright 2025 Tobias Senti
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

NumWarps_range=(1 2 4 8 16)
InflightInstructionsPerWarp_range=(2 4 8 16)

for NumWarp in ${NumWarps_range[@]}
do
    for InflightInstructionsPerWarp in ${InflightInstructionsPerWarp_range[@]}
    do
        TblocksToLaunch=$((NumWarp * InflightInstructionsPerWarp + 1))
        if [ $TblocksToLaunch -gt 256 ]; then
            TblocksToLaunch=256
        fi
        echo "Running simulation for NumWarp: $NumWarp, InflightInstructionsPerWarp: $InflightInstructionsPerWarp, TblocksToLaunch: $TblocksToLaunch"
        result=$(make tb_compute_unit VERILATOR_ARGS="-GNumWarps=$NumWarp -GInflightInstrPerWarp=$InflightInstructionsPerWarp -GTblocksToLaunch=$TblocksToLaunch -GMaxSimCycles=4000")
        if [ $? -eq 0 ]; then
            echo "$result" | grep -A1 "All thread blocks done."
            echo "Passed!"
        else
            echo "$result" > failure.log
            cat failure.log
            echo "Failed!"
            exit 1
        fi
    done
    echo ""
done

echo "All simulations passed"
