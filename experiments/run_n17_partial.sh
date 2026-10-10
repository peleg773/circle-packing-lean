#!/bin/bash
# n = 17, rigorous (ringbb_v3 = certified B&B with cheaper certified contraction bound), cases k = 6..9 and the
# record case k = 7 with the survivor certification.  k = 10, 11, 12 are run separately (long).
set -e
cd "$(dirname "$0")"
export NUMBA_CACHE_DIR="$(pwd)/out/n17/numba_cache_$(date +%s)"
export OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 OMP_NUM_THREADS=1 NUMEXPR_NUM_THREADS=1
mkdir -p out/n17 "$NUMBA_CACHE_DIR"
L=out/n17
RHO=3.79203374831058
echo "start $(date)" > $L/TIMES.txt
python local_cert_sym.py 17 > $L/localcert_n17.log 2>&1
python verify_L4.py $RHO > $L/L4_n17.log 2>&1
python ringbb_v3.py 17 $RHO 7 7 0.00001 selfcontained > $L/bb_n17_record.log 2>&1
echo "record B&B done $(date)" >> $L/TIMES.txt
python verify_final_arb3.py 17 $RHO 7 out/v3_surv_n17_k7_selfcontained.npy $L/final_check2_n17.json > $L/final_check2_n17.log 2>&1
echo "record check done $(date)" >> $L/TIMES.txt
python ringbb_v3.py 17 $RHO 6 6 0.02 selfcontained > $L/bb_n17_k6.log 2>&1
python ringbb_v3.py 17 $RHO 8 9 0.02 selfcontained > $L/bb_n17_k8_9.log 2>&1
echo "k<=9 done $(date)" >> $L/TIMES.txt
