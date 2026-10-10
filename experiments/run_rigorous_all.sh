#!/bin/bash
# Full rigorous pipeline for n = 15 and n = 16.
# Usage: bash run_rigorous_all.sh   (from experiments/; logs go to out/)
set -e
cd "$(dirname "$0")"
mkdir -p out
# --- local certificates (arb) ---
python local_cert.py 15 > out/rig_localcert_n15.log 2>&1
python local_cert.py 16 > out/rig_localcert_n16.log 2>&1
# --- lemma L4 (measure-bound disjointness) ---
python verify_L4.py 3.52135696470617 > out/rig_L4_n15.log 2>&1
python verify_L4.py 3.61542559487320 > out/rig_L4_n16.log 2>&1
# --- rigorous B&B: n = 15 ---
python ringbb_rig.py 15 3.52135696470617 5 5 0.00001 > out/rig_bb_n15_k5.log 2>&1
python verify_final_arb.py 15 3.52135696470617 5 out/rigsurv_n15_k5.npy > out/rig_final_n15.log 2>&1
python ringbb_rig.py 15 3.52135696470617 6 10 0.02 > out/rig_bb_n15_k6_10.log 2>&1
# --- rigorous B&B: n = 16 ---
python ringbb_rig.py 16 3.61542559487320 5 5 0.00001 > out/rig_bb_n16_k5.log 2>&1
python verify_final_arb.py 16 3.61542559487320 5 out/rigsurv_n16_k5.npy > out/rig_final_n16.log 2>&1
python ringbb_rig.py 16 3.61542559487320 6 11 0.02 > out/rig_bb_n16_k6_11.log 2>&1
echo "ALL DONE" > out/rig_ALL_DONE.txt
