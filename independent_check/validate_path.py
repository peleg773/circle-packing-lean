"""
Soundness validation: for explicit feasible configurations, follow the B&B path of boxes
that contain the configuration (always descending into the child containing it) and
check that (i) no box on the path is ever pruned and (ii) contraction never removes the
configuration from its box.  Run at several rho for k = 5..10.
"""
import sys, json, math, time
import numpy as np
from core import constants, EPS_DB, excess_slack
import bnb2 as BB
from configs import unpack, check_config, random_feasible, canonical


def params(rho, k):
    RI_hi, db_lo, rho_m2 = constants(rho)
    db_hi = db_lo + 2 * EPS_DB
    m = 15 - k
    slack_hi = excess_slack(rho, m, db_lo)
    return RI_hi, db_lo, db_hi, rho_m2, slack_hi, m


def inside(B, C, tol=1e-12):
    for i in range(len(C)):
        s, p = C[i]
        if not (B[i, 0] - tol <= s <= B[i, 1] + tol):
            return False
        if not (B[i, 2] - tol <= p <= B[i, 3] + tol):
            return False
    return True


def follow(C, k, rho, tol=1e-7, maxsteps=100000):
    RI_hi, db_lo, db_hi, rho_m2, slack_hi, m = params(rho, k)
    B = BB.root_box2(k, RI_hi)
    arc_a = np.empty(k + 2); arc_b = np.empty(k + 2); W = np.empty((8, k + 4))
    if not inside(B, C):
        return "config not in root box"
    for step in range(maxsteps):
        code = BB.check_node2(B, k, m, rho, rho_m2, db_lo, db_hi, slack_hi, BB.R_M,
                              arc_a, arc_b, W)
        if code != BB.C_ALIVE:
            return f"PRUNED (code {code}) at step {step}"
        if not inside(B, C):
            return f"CONTRACTION LOST CONFIG at step {step}"
        best, bi, bd = BB.choose_split(B, k)
        if best < tol:
            return "ok"
        mid = 0.5 * (B[bi, bd] + B[bi, bd + 1])
        v = C[bi, 0] if bd == 0 else C[bi, 1]
        if v <= mid:
            B[bi, bd + 1] = mid
        else:
            B[bi, bd] = mid
    return "ok (maxsteps)"


if __name__ == "__main__":
    best = json.load(open("rho_crit_configs.json"))
    t0 = time.time()
    nbad = 0
    ntest = 0
    for k in range(5, 11):
        rc, x = best[str(k)]
        x = np.array(x)
        rho0, P, a = unpack(x, k, 15 - k)
        # optimized (near-critical) configuration at slightly larger rho
        for drho in (1e-8, 1e-6, 1e-4):
            rho = rho0 + drho
            sl = check_config(P, a, rho)
            C = canonical(P)
            r = follow(C, k, rho)
            ntest += 1
            if not r.startswith("ok"):
                nbad += 1
            print(f"k={k} rho={rho:.10f} (crit+{drho:g}) slack={sl:.2e}: {r}")
        # random feasible configurations at larger rho
        for drho in (0.005, 0.02, 0.1, 0.3):
            rho = rc + drho
            cnt = 0
            for seed in range(40):
                res = random_feasible(k, rho, seed, tries=5)
                if res is None:
                    continue
                P2, a2 = res
                C = canonical(P2)
                r = follow(C, k, rho)
                ntest += 1
                cnt += 1
                if not r.startswith("ok"):
                    nbad += 1
                    print(f"  BAD k={k} rho={rho} seed={seed}: {r}")
            print(f"k={k} rho={rho:.4f}: tested {cnt} random feasible configurations")
    print(f"total tests {ntest}, failures {nbad}, time {time.time()-t0:.1f}s")
