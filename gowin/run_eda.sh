#!/bin/bash

for i in {1..5}; do
    LD_LIBRARY_PATH=$1/lib $1/bin/gw_sh $2
    code=$?
    if [ $code -eq 0 ]; then
        echo "Run $i successful."
        break
    elif [ $code -eq 2 ]; then
        echo "Run failed due to a synthesis warning."
        break
    else
        echo "Run $i failed, retrying..."
        sleep 5
    fi
done
