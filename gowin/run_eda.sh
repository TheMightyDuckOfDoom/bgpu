#!/bin/bash

for i in {1..5}; do
    LD_LIBRARY_PATH=$1/lib $1/bin/gw_sh $2
    if [ $? -eq 0 ]; then
        echo "Run $i successful."
        break
    else
        echo "Run $i failed, retrying..."
        sleep 5
    fi
done