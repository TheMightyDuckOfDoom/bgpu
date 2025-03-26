#!/bin/bash

NumWarps_range=(2 4 8 16)
WaitBufferSizePerWarp_range=(2 4 8)

for NumWarp in ${NumWarps_range[@]}
do
    for WaitBufferSizePerWarp in ${WaitBufferSizePerWarp_range[@]}
    do
        InflightInstructionsPerWarp=$((2 * WaitBufferSizePerWarp))
        result=$(make tb_compute_unit VERILATOR_ARGS="-GNumWarps=$NumWarp -GWaitBufferSizePerWarp=$WaitBufferSizePerWarp -GInflightInstrPerWarp=$InflightInstructionsPerWarp -GMaxSimCycles=2000")
        if [ $? -eq 0 ]; then
            echo "Simulation passed for NumWarp: $NumWarp, WaitBufferSizePerWarp: $WaitBufferSizePerWarp InflightInstructionsPerWarp: $InflightInstructionsPerWarp"
        else
            echo "$result"
            echo "Simulation failed for NumWarp: $NumWarp, WaitBufferSizePerWarp: $WaitBufferSizePerWarp InflightInstructionsPerWarp: $InflightInstructionsPerWarp"
            exit 1
        fi
    done
    echo ""
done

echo "All simulations passed"
