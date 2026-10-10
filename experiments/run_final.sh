#!/bin/bash
# FINAL certified pipeline (literature-free radius bounds, fresh numba cache, audit logs).
# Usage: bash run_final.sh       (from experiments/; all logs and JSON summaries in out/final/)
set -e
cd "$(dirname "$0")"
export NUMBA_CACHE_DIR="$(pwd)/out/final/numba_cache_$(date +%s)"
# one BLAS/OpenMP thread per process: otherwise each of the 20 worker processes commits ~1 GB (OpenBLAS buffers)
export OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 OMP_NUM_THREADS=1 NUMEXPR_NUM_THREADS=1
mkdir -p out/final "$NUMBA_CACHE_DIR"
L=out/final
echo "start $(date)" > $L/TIMES.txt
# 1. local certificates (arb)
python local_cert.py 15        > $L/localcert_n15.log 2>&1
python local_cert.py 16        > $L/localcert_n16.log 2>&1
python local_cert_sym.py 14    > $L/localcert_n14.log 2>&1
# 2. lemma L4
python verify_L4.py 3.32842855486084 > $L/L4_n14.log 2>&1
python verify_L4.py 3.52135696470617 > $L/L4_n15.log 2>&1
python verify_L4.py 3.61542559487320 > $L/L4_n16.log 2>&1
# 3. literature-free radius bounds rho_m > L_m, m = 8..13
python prove_radius_bounds.py 13 1e-6 > $L/radius_bounds.log 2>&1
echo "certificates+bounds done $(date)" >> $L/TIMES.txt
# 4. main branch and bound (selfcontained radius table), record case first, then all other k
for spec in "14 3.32842855486084 4 9" "15 3.52135696470617 5 10" "16 3.61542559487320 5 11"; do
  set -- $spec; n=$1; rho=$2; k0=$3; k1=$4
  python ringbb_final.py $n $rho $k0 $k0 0.00001 selfcontained > $L/bb_n${n}_record.log 2>&1
  python verify_final_arb2.py $n $rho $k0 out/final_surv_n${n}_k${k0}_selfcontained.npy $L/final_check2_n${n}.json > $L/final_check2_n${n}.log 2>&1
  python ringbb_final.py $n $rho $((k0+1)) $k1 0.02 selfcontained > $L/bb_n${n}_other.log 2>&1
  echo "n=$n done $(date)" >> $L/TIMES.txt
done
echo "ALL DONE $(date)" >> $L/TIMES.txt
