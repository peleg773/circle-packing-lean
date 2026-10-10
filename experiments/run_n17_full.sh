#!/bin/bash
# n = 17: full rigorous pipeline with ringbb_v4 (certified B&B, deep-last split rule).
set -e
cd "$(dirname "$0")"
export NUMBA_CACHE_DIR="$(pwd)/out/n17/numba_cache_$(date +%s)"
export OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 OMP_NUM_THREADS=1 NUMEXPR_NUM_THREADS=1
mkdir -p out/n17 "$NUMBA_CACHE_DIR"
L=out/n17
RHO=3.79203374831058
echo "start $(date)" > $L/TIMES.txt
sha256sum ringbb_v4.py ringbb_v3.py ringbb_final.py ringbb2.py rigmath.py rigmath_fast.py rig_consts.json local_cert_sym.py verify_L4.py verify_final_arb3.py > $L/SOURCE_HASHES.txt
python local_cert_sym.py 17 > $L/localcert_n17.log 2>&1
python verify_L4.py $RHO > $L/L4_n17.log 2>&1
python ringbb_v4.py 17 $RHO 7 7 0.00001 selfcontained > $L/bb_n17_record.log 2>&1
echo "record B&B done $(date)" >> $L/TIMES.txt
python verify_final_arb3.py 17 $RHO 7 out/v4_surv_n17_k7_selfcontained.npy $L/final_check3_n17.json > $L/final_check3_n17.log 2>&1
echo "record check done $(date)" >> $L/TIMES.txt
python ringbb_v4.py 17 $RHO 6 6 0.02 selfcontained > $L/bb_n17_k6.log 2>&1
for k in 8 9 10 11 12; do
  python ringbb_v4.py 17 $RHO $k $k 0.02 selfcontained > $L/bb_n17_k$k.log 2>&1
  echo "k=$k done $(date)" >> $L/TIMES.txt
done
echo "ALL DONE $(date)" >> $L/TIMES.txt
