"""
Threshold validation: for each k, run the full B&B (single process, coarse tolerance) at
rho values around the heuristic critical radius rho_c(k) (explicit configuration known).
Soundness requires survivors for every rho >= rho_c(k); we bisect for the smallest rho
at which the B&B still finds a survivor (the B&B threshold must be <= rho_c(k)).
"""
import sys, json, math, time
import numpy as np
from core import constants, EPS_DB, excess_slack
import bnb2 as BB


def run(rho, k, tol, budget):
    m = 15 - k
    RI_hi, db_lo, rho_m2 = constants(rho)
    db_hi = db_lo + 2 * EPS_DB
    slack_hi = excess_slack(rho, m, db_lo)
    root = BB.root_box2(k, RI_hi)[None].copy()
    surv = np.zeros((10, k, 4))
    stats = np.zeros(BB.NSTAT, dtype=np.int64)
    pent = np.array([1.0, 0.0, 0.0])
    nodes, nsurv, done, rest, rvol = BB.dfs2(root, np.ones(1), k, m, rho, rho_m2, db_lo,
                                             db_hi, slack_hi, BB.R_M, tol, budget, surv,
                                             stats, 0, pent, 1)
    return nodes, nsurv, done, rest.shape[0], surv[:min(nsurv, 1)]


if __name__ == "__main__":
    best = json.load(open("rho_crit_configs.json"))
    tol = float(sys.argv[1]) if len(sys.argv) > 1 else 1e-3
    ks = [int(x) for x in sys.argv[2:]] or [5, 6, 7, 8, 9, 10]
    for k in ks:
        rc = best[str(k)][0]
        t0 = time.time()
        # must find survivors just above rc
        nodes, nsurv, done, nrest, sv = run(rc + 1e-7, k, tol, int(5e7))
        print(f"k={k} rho_c={rc:.8f}: at rho_c+1e-7 -> survivors={nsurv} nodes={nodes} "
              f"done={done:.4f} ({time.time()-t0:.0f}s)", flush=True)
        # bisection for the B&B threshold in [3.50, rc+1e-7]
        lo, hi = 3.50, rc + 1e-7
        n0, s0, d0, r0, _ = run(lo, k, tol, int(5e7))
        if s0 > 0:
            print(f"   survivors already at rho={lo}")
            continue
        for it in range(14):
            mid = 0.5 * (lo + hi)
            nodes, nsurv, done, nrest, sv = run(mid, k, tol, int(5e7))
            if nsurv > 0:
                hi = mid
            elif nrest == 0:
                lo = mid
            else:
                print("   budget exhausted at", mid)
                break
        print(f"   B&B threshold (tol={tol}) in [{lo:.6f}, {hi:.6f}]  vs heuristic rho_c={rc:.6f}"
              f"  ({time.time()-t0:.0f}s)", flush=True)
