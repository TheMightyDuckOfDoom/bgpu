#!/bin/bash
LD_PRELOAD=/lib/x86_64-linux-gnu/libfreetype.so LD_LIBRARY_PATH=$1/lib $1/bin/gw_sh $2
