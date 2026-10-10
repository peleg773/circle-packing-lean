#!/bin/bash
# Rigorous pipeline for n = 16 using ringbb_rig_fast.py (identical search tree to ringbb_rig.py, cached contraction bounds)
cd "$(dirname "$0")"
python ringbb_rig_fast.py 16 3.61542559487320 5 5 0.00001 > out/rigfast_bb_n16_k5.log 2>&1
python verify_final_arb.py 16 3.61542559487320 5 out/rigfastsurv_n16_k5.npy > out/rigfast_final_n16.log 2>&1
python ringbb_rig_fast.py 16 3.61542559487320 6 11 0.02 > out/rigfast_bb_n16_k6_11.log 2>&1
echo DONE > out/rigfast_n16_DONE.txt
