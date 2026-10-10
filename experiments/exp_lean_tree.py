"""Tree-size experiment for the Lean port (planning only, not part of any proof).
Same rigorous B&B as ringbb_v4.py, but with switchable pruning rules, to see which rules the Lean checker needs:
  flags: C = contraction (L9), M = measure bound (L5/L4).  P1 (pairs), P2 (greedy), P4 (ordering) always on.
Usage: python exp_lean_tree.py n rho kmin kmax tol flags [wdeep] [nworkers]
"""
import sys, os, math, time
import numpy as np
import numba as nb
import ringbb_v4 as V
import ringbb2 as F
from rigmath import dn, up, TWO_PI_HI


@nb.njit(cache=True)
def box_ok_flags(slo, shi, plo, phi, k, n, rho, delta_lo, delta_hi, RI_hi, rhoM, use_c, use_m):
    for j in range(k):
        if shi[j] > RI_hi:
            shi[j] = RI_hi
        lb = rhoM[k - j]
        if slo[j] < lb:
            slo[j] = lb
        if j > 0 and shi[j] > shi[j - 1]:
            shi[j] = shi[j - 1]
        if slo[j] > shi[j]:
            return 4
    for j in range(k - 1, 0, -1):
        if slo[j - 1] < slo[j]:
            slo[j - 1] = slo[j]
        if slo[j - 1] > shi[j - 1]:
            return 4
    if use_c:
        if not V.contract_rig(slo, shi, plo, phi, k):
            return 1
    for a in range(k):
        for b in range(a + 1, k):
            if F.maxdist2(slo[a], shi[a], plo[a], phi[a], slo[b], shi[b], plo[b], phi[b]) < 4.0 - 1e-7:
                if V.maxdist2_hi_rig(slo[a], shi[a], plo[a], phi[a], slo[b], shi[b], plo[b], phi[b]) < 4.0:
                    return 1
    if use_m:
        deltaf = 0.5 * (delta_lo + delta_hi)
        budget = 2.0 * math.pi - (n - k) * deltaf
        tot = 0.0
        for j in range(k):
            e = 2.0 * F.theta_of(slo[j], rho) - deltaf
            if e > 0.0:
                tot += e
        if tot > budget + 1e-7:
            tl = 0.0
            for j in range(k):
                e = dn(dn(2.0 * V.theta_lo_rig(slo[j], rho)) - delta_hi)
                if e > 0.0:
                    tl = dn(tl + e)
            bh = up(TWO_PI_HI - dn((n - k) * delta_lo))
            if tl > bh:
                return 5
    deltaf = 0.5 * (delta_lo + delta_hi)
    if F.bmax_box(slo, shi, plo, phi, k, rho, deltaf, True) < n - k:
        if V.bmax_rig(slo, plo, phi, k, rho, delta_lo) < n - k:
            return 2
    return 0


@nb.njit(cache=True)
def run_bb(n, k, rho, delta_lo, delta_hi, RI_hi, rhoM, tol, b0, wdeep, use_c, use_m, maxdepth_out):
    cap = 1 << 16
    stack = np.empty((cap, 4 * k))
    depth = np.zeros(cap, np.int64)
    stack[0] = b0; sp = 1
    nproc = 0
    reasons = np.zeros(6, np.int64)
    nsurv = 0
    maxd = 0
    while sp > 0:
        sp -= 1
        bx = stack[sp].copy(); d = depth[sp]
        if d > maxd:
            maxd = d
        nproc += 1
        slo = bx[0:k]; shi = bx[k:2 * k]; plo = bx[2 * k:3 * k]; phi = bx[3 * k:4 * k]
        r = box_ok_flags(slo, shi, plo, phi, k, n, rho, delta_lo, delta_hi, RI_hi, rhoM, use_c, use_m)
        if r > 0:
            reasons[r] += 1
            continue
        jw, cw, w = F.choose_split(slo, shi, plo, phi, k)
        j, c = V.choose_split_deeplast(slo, shi, plo, phi, k, rho - 2.0, wdeep)
        if w < tol or sp + 2 >= cap:
            nsurv += 1
            continue
        b1 = bx.copy(); b2 = bx.copy()
        if c == 0:
            mid = 0.5 * (slo[j] + shi[j]); b1[k + j] = mid; b2[j] = mid
        else:
            mid = 0.5 * (plo[j] + phi[j]); b1[3 * k + j] = mid; b2[2 * k + j] = mid
        stack[sp] = b1; depth[sp] = d + 1; sp += 1
        stack[sp] = b2; depth[sp] = d + 1; sp += 1
    maxdepth_out[0] = maxd
    return nproc, reasons, nsurv


def _worker(args):
    n, k, rho, P, tol, bx, wdeep, use_c, use_m = args
    dl, dh, rih, rm = P
    md = np.zeros(1, np.int64)
    r = run_bb(n, k, rho, dl, dh, rih, rm, tol, bx, wdeep, use_c, use_m, md)
    return r[0], r[1], r[2], int(md[0])


def main():
    n = int(sys.argv[1]); rho = float(sys.argv[2]); kmin = int(sys.argv[3]); kmax = int(sys.argv[4])
    tol = float(sys.argv[5]); flags = sys.argv[6]
    wdeep = float(sys.argv[7]) if len(sys.argv) > 7 else 0.25
    nw = int(sys.argv[8]) if len(sys.argv) > 8 else 8
    use_c = "C" in flags; use_m = "M" in flags
    P = V.rigorous_params(n, rho, "selfcontained")
    from multiprocessing import Pool
    for k in range(kmin, kmax + 1):
        boxes = V.presplit(n, k, rho, P, 256)
        t0 = time.time()
        with Pool(nw) as pool:
            res = pool.map(_worker, [(n, k, rho, P, tol if k != 5 or n != 15 else tol, b, wdeep, use_c, use_m)
                                     for b in boxes], chunksize=1)
        nproc = sum(r[0] for r in res); reasons = sum(r[1] for r in res); ns = sum(r[2] for r in res)
        md = max(r[3] for r in res)
        print(f"n={n} k={k} flags={flags} wdeep={wdeep}: presplit={len(boxes)} boxes={nproc:,} "
              f"reasons[pair,bnd,-,order,meas]={list(reasons[1:])} surv={ns} maxdepth={md} t={time.time()-t0:.1f}s",
              flush=True)


if __name__ == "__main__":
    main()
