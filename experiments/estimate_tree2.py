"""Knuth estimator with a selectable split heuristic. Usage: python estimate_tree2.py n rho k probes heuristic [thresh]"""
import sys, math, time
import numpy as np
import ringbb2 as F
from split_heuristics import choose_split_conflict, choose_split_deep_last


def split_with(b, k, j, c):
    b1 = b.copy(); b2 = b.copy()
    if c == 0:
        mid = 0.5 * (b[j] + b[k + j]); b1[k + j] = mid; b2[j] = mid
    else:
        mid = 0.5 * (b[2 * k + j] + b[3 * k + j]); b1[3 * k + j] = mid; b2[2 * k + j] = mid
    return b1, b2


def main():
    n = int(sys.argv[1]); rho = float(sys.argv[2]); k = int(sys.argv[3]); probes = int(sys.argv[4]); heur = sys.argv[5]
    thresh = float(sys.argv[6]) if len(sys.argv) > 6 else 9.0
    tol = 0.02
    delta = 2 * math.asin(1 / rho); RI = math.sqrt(rho * rho - 4)
    roots = F.presplit(n, k, rho, 4096)
    rng = np.random.default_rng(1)
    est = []; t0 = time.time()
    for p in range(probes):
        b = roots[rng.integers(len(roots))].copy()
        weight = float(len(roots)); total = weight; depth = 0
        while True:
            r = F.box_ok(b[0:k], b[k:2 * k], b[2 * k:3 * k], b[3 * k:4 * k], k, n, rho, delta, RI, F.RHO_M, False)
            if r > 0:
                break
            slo = b[0:k]; shi = b[k:2 * k]; plo = b[2 * k:3 * k]; phi = b[3 * k:4 * k]
            if heur == "widest":
                j, c, w = F.choose_split(slo, shi, plo, phi, k)
            elif heur == "deeplast":
                j, c, w = choose_split_deep_last(slo, shi, plo, phi, k, rho - 2.0, thresh)
            else:
                j, c, w = choose_split_conflict(slo, shi, plo, phi, k, thresh)
            jw, cw, ww = F.choose_split(slo, shi, plo, phi, k)
            if ww < tol:
                break
            b1, b2 = split_with(b, k, j, c)
            b = b1 if rng.random() < 0.5 else b2
            weight *= 2.0; total += weight; depth += 1
            if depth > 600:
                break
        est.append(total)
    est = np.array(est)
    print(f"n={n} k={k} heuristic={heur} thresh={thresh}: est nodes {est.mean():.3e} (+- {est.std()/math.sqrt(len(est)):.1e}) median {np.median(est):.2e} ({time.time()-t0:.1f}s)")


if __name__ == "__main__":
    main()
