#!/bin/bash
# n = 18 exploration with the FLOAT B&B (not a proof).  rho_19 = 1/sin(pi/12) = 3.8637033051562732
cd "$(dirname "$0")"
export OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 OMP_NUM_THREADS=1
mkdir -p out/n18
# (a) at rho_19 (+1e-12 relative): which interior structures survive (k = 6..13)?
python ringbb2.py 18 3.8637033051562770 6 13 0.005 3e10 > out/n18/float_at_rho19.log 2>&1
# (b) at rho_19 (1 - 1e-4): does everything die?  (cost estimate for the bound d_18 <= d_19 (1 + 1e-4))
python ringbb2.py 18 3.863316934825758 7 13 0.005 3e10 > out/n18/float_eta1e-4.log 2>&1
echo DONE > out/n18/DONE.txt
