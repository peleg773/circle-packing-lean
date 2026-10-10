#!/bin/bash
set -e
cd "$(dirname "$0")"
export NUMBA_CACHE_DIR="$(pwd)/out/n18/numba_cache_k78_$(date +%s)"
export OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 OMP_NUM_THREADS=1 NUMEXPR_NUM_THREADS=1
export RINGBB_SURV_CAP=200000
mkdir -p out/n18 "$NUMBA_CACHE_DIR"
L=out/n18
RHO=3.8637033051562770
echo "start k78 $(date)" >> $L/TIMES.txt
python ringbb_v4.py 18 $RHO 7 7 0.01 selfcontained > $L/bb_n18_k7.log 2>&1
python ringbb_v4.py 18 $RHO 8 8 0.01 selfcontained > $L/bb_n18_k8.log 2>&1
echo "k78 done $(date)" >> $L/TIMES.txt
