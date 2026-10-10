"""Knuth estimate for the OUTER-ONLY relaxation (exploration): for true interior count k, consider only the
k_o outer interior points (radius in (rho-2, R_I]); deep points (radius <= rho-2, at most M(rho-2) of them) are
dropped except through the counting bounds s_j >= L_{k-j}.  Boundary needs B = n - k points.
Usage: python estimate_outer.py n rho k k_o probes"""
import sys, math, time
import numpy as np
import ringbb2 as F


def main():
    n, rho, k, ko, probes = int(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
    delta = 2 * math.asin(1 / rho); RI = math.sqrt(rho * rho - 4)
    rhoM = F.RHO_M.copy()
    sh = np.zeros(40); full = np.concatenate([rhoM, np.full(40 - len(rhoM), rhoM[-1])])
    for i in range(40):
        sh[i] = full[min(i + (k - ko), 39)]
    n_code = n - k + ko
    # initial box: all ko points outer
    b0 = np.empty(4 * ko)
    for j in range(ko):
        b0[j] = rho - 2.0; b0[ko + j] = RI; b0[2 * ko + j] = 0.0; b0[3 * ko + j] = 2 * math.pi
    b0[3 * ko] = 0.0
    if ko >= 2:
        b0[3 * ko + 1] = math.pi
    # presplit
    boxes = [b0]
    while len(boxes) < 4096:
        new = []
        for bx in boxes:
            b = bx.copy()
            if F.box_ok(b[0:ko], b[ko:2*ko], b[2*ko:3*ko], b[3*ko:4*ko], ko, n_code, rho, delta, RI, sh, False) > 0:
                continue
            b1, b2 = F.split_box(b, ko); new += [b1, b2]
        if not new:
            break
        boxes = new
    if not boxes or (len(boxes) == 1 and F.box_ok(boxes[0][0:ko].copy(), boxes[0][ko:2*ko].copy(), boxes[0][2*ko:3*ko].copy(), boxes[0][3*ko:4*ko].copy(), ko, n_code, rho, delta, RI, sh, False) > 0):
        print(f"n={n} k={k} k_o={ko}: pruned during presplit"); return
    rng = np.random.default_rng(1)
    est = []; t0 = time.time()
    for p in range(probes):
        b = boxes[rng.integers(len(boxes))].copy()
        weight = float(len(boxes)); total = weight; depth = 0
        while True:
            r = F.box_ok(b[0:ko], b[ko:2*ko], b[2*ko:3*ko], b[3*ko:4*ko], ko, n_code, rho, delta, RI, sh, False)
            if r > 0:
                break
            j, c, w = F.choose_split(b[0:ko], b[ko:2*ko], b[2*ko:3*ko], b[3*ko:4*ko], ko)
            if w < 0.02:
                break
            b1, b2 = F.split_box(b, ko); b = b1 if rng.random() < 0.5 else b2
            weight *= 2; total += weight; depth += 1
        est.append(total)
    est = np.array(est)
    print(f"n={n} k={k} k_o={ko}: presplit={len(boxes)} est nodes {est.mean():.3e} (+- {est.std()/math.sqrt(len(est)):.1e}) ({time.time()-t0:.1f}s)")


if __name__ == "__main__":
    main()
