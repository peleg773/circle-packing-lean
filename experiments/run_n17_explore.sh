#!/bin/bash
# n = 17 exploration with the FLOAT B&B (fast filter; NOT a proof): cost estimate per k and survivor structure.
cd "$(dirname "$0")"
mkdir -p out/n17
OPENBLAS_NUM_THREADS=1 python ringbb2.py 17 3.79203374831058 7 7 0.00001 2e11 > out/n17/float_k7_record.log 2>&1
OPENBLAS_NUM_THREADS=1 python ringbb2.py 17 3.79203374831058 6 6 0.02 2e11 > out/n17/float_k6.log 2>&1
OPENBLAS_NUM_THREADS=1 python ringbb2.py 17 3.79203374831058 8 12 0.02 2e11 > out/n17/float_k8_12.log 2>&1
echo DONE > out/n17/DONE.txt
