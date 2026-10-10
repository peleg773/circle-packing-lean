"""Positive control: run the rigorous B&B at a container radius slightly ABOVE that of a known competitor
local optimum; the competitor's canonical interior configuration MUST lie in some surviving box.
(A pruning bug would make it disappear.)

Usage: python positive_control.py n cluster_index msfile tol
"""
import sys, json, math, os
import numpy as np
import ringbb_rig as RG
from soundness_test import canonical_interior


def main():
    n = int(sys.argv[1]); ci = int(sys.argv[2]); fn = sys.argv[3]; tol = float(sys.argv[4])
    data = json.load(open(fn))
    cl = data["clusters"][ci]
    P = np.array(cl["example"]["P"])
    D = np.sqrt(((P[:, None] - P[None]) ** 2).sum(-1)); np.fill_diagonal(D, 9); d = D.min()
    C = P * (2 * (1 + 1e-7) / d)
    rho_c = np.hypot(C[:, 0], C[:, 1]).max()
    rho = rho_c * (1 + 1e-9)
    s, psi, nb, feas = canonical_interior(C, rho)
    k = len(s)
    print(f"competitor: d={d:.10f} rho_c={rho_c:.8f} k={k} B={nb} feasible_min_dist={feas:.9f}")
    print("  canonical s  =", np.round(s, 5)); print("  canonical psi=", np.round(psi, 5))
    nproc, reasons, surv, unf, dt, nb0 = RG.solve_k(n, k, rho, tol)
    print(f"  B&B at rho={rho:.10f}, k={k}: boxes={nproc:,} survivors={len(surv)} unfinished={unf} overflow={reasons[0]} time={dt:.1f}s")
    hit = 0
    for bx in surv:
        slo = bx[0:k]; shi = bx[k:2*k]; plo = bx[2*k:3*k]; phi = bx[3*k:4*k]
        if np.all(slo <= s + 1e-12) and np.all(s <= shi + 1e-12) and np.all(plo <= psi + 1e-12) and np.all(psi <= phi + 1e-12):
            hit += 1
    print(f"  survivor boxes containing the competitor: {hit}  -> {'PASS' if hit > 0 else 'FAIL'}")


if __name__ == "__main__":
    main()
