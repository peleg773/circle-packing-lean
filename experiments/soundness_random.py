"""Randomised soundness test: generate many strictly feasible configurations for n points at container
radius rho slightly above rho* (several slacks), then check that NO B&B pruning rule (rigorous and float)
discards their canonical interior point-box or random small boxes around it.

Usage: python soundness_random.py n rho_star nconf seed
"""
import sys, math, time
import numpy as np
from multiprocessing import Pool
from search_lib import penalty_minimize, random_disk, min_sep
import ringbb_final as RG
import ringbb2 as F
from soundness_test import canonical_interior


def gen(args):
    n, rho_star, seed = args
    rng = np.random.default_rng(seed)
    out = []
    for slack in (1e-3, 3e-3, 1e-2, 3e-2, 1e-1):
        d_target = 2.0 / (rho_star * (1 + slack))        # point normalisation separation
        for rep in range(3):
            P = random_disk(n, rng)
            for frac in (0.85, 0.95, 1.0):
                P, E = penalty_minimize(P, d_target * frac)
            P, E = penalty_minimize(P, d_target * 1.000001)
            r = np.hypot(P[:, 0], P[:, 1]).max()
            dm = min_sep(P)
            if r <= 1.0 + 1e-12 and dm >= d_target:
                # unit circles: scale so that min distance = 2(1+1e-7)
                C = P * (2 * (1 + 1e-7) / dm)
                out.append(C)
    return out


def main():
    n = int(sys.argv[1]); rho_star = float(sys.argv[2]); nconf = int(sys.argv[3]); seed = int(sys.argv[4])
    t0 = time.time()
    with Pool(19) as pool:
        res = pool.map(gen, [(n, rho_star, seed * 100000 + i) for i in range(nconf)])
    confs = [c for r in res for c in r]
    print(f"generated {len(confs)} strictly feasible configurations in {time.time()-t0:.1f}s")
    rng = np.random.default_rng(seed)
    bad = 0; ntest = 0; ks = {}
    for C in confs:
        rho = np.hypot(C[:, 0], C[:, 1]).max() * (1 + 1e-12)
        s, psi, nb, feas = canonical_interior(C, rho)
        k = len(s)
        if k < 2 or feas < 2:
            continue
        ks[k] = ks.get(k, 0) + 1
        dl, dh, rih, rm = RG.rigorous_params(n, rho, 'selfcontained')
        delta = 2 * math.asin(1 / rho); RI = math.sqrt(rho * rho - 4)
        for trial in range(4):
            if trial == 0:
                slo = s.copy(); shi = s.copy(); plo = psi.copy(); phi = psi.copy()
            else:
                w = 10 ** rng.uniform(-7, -1)
                slo = np.maximum(s - rng.uniform(0, w, k), 0.0); shi = s + rng.uniform(0, w, k)
                plo = psi - rng.uniform(0, w, k); phi = psi + rng.uniform(0, w, k)
                plo[0] = 0.0; phi[0] = 0.0
                plo[1] = max(plo[1], 0.0); phi[1] = min(phi[1], math.pi)
            a1, a2, a3, a4 = slo.copy(), shi.copy(), plo.copy(), phi.copy()
            r1 = RG.box_ok_rig(a1, a2, a3, a4, k, n, rho, dl, dh, rih, rm)
            if r1 == 0 and not (np.all(a1 <= s + 1e-15) and np.all(s <= a2 + 1e-15) and np.all(a3 <= psi + 1e-15) and np.all(psi <= a4 + 1e-15)):
                bad += 1
                print("  CONTRACTION LOST FEASIBLE POINT", k, trial)
            r2 = F.box_ok(slo.copy(), shi.copy(), plo.copy(), phi.copy(), k, n, rho, delta, RI, F.RHO_M, False)
            ntest += 1
            if r1 != 0 or r2 != 0:
                bad += 1
                if bad < 10:
                    print(f"  PRUNED FEASIBLE k={k} rho={rho:.6f} trial={trial} rig={r1} float={r2}")
    print(f"n={n}: tests={ntest} bad={bad}  k-distribution={dict(sorted(ks.items()))}")


if __name__ == "__main__":
    main()
