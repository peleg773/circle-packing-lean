#!/bin/bash
# n = 18: (1) prove L_14 (needed for k <= 13), (2) rigorous v4 B&B at rho_test = rho_19+ for k = 7..13 (B <= 11;
# B = 12 is impossible for a configuration with rho < rho_19 after scaling+push-out, see n18_analysis.md).
set -e
cd "$(dirname "$0")"
export NUMBA_CACHE_DIR="$(pwd)/out/n18/numba_cache_$(date +%s)"
export OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 OMP_NUM_THREADS=1 NUMEXPR_NUM_THREADS=1
export RINGBB_SURV_CAP=200000
mkdir -p out/n18 "$NUMBA_CACHE_DIR"
L=out/n18
echo "start $(date)" > $L/TIMES.txt
python prove_radius_bounds.py 14 1e-6 > $L/radius_bounds_m14.log 2>&1
echo "L_14 done $(date)" >> $L/TIMES.txt
RHO=3.8637033051562770
for k in 7 8 9 10 11 12 13; do
  python ringbb_v4.py 18 $RHO $k $k 0.01 selfcontained > $L/bb_n18_k$k.log 2>&1
  echo "k=$k done $(date)" >> $L/TIMES.txt
done
echo "ALL DONE $(date)" >> $L/TIMES.txt
