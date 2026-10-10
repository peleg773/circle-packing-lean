"""Knuth's random-probe estimator of the B&B tree size (float filters only; for cost planning, not a proof).
For each probe: start from a random presplit box, repeatedly evaluate the box; if pruned stop; else split and
descend into a uniformly random child, multiplying the weight by the number of surviving children (2).
The mean of sum_{levels} prod(branching) is an unbiased estimate of the number of processed nodes.
Usage: python estimate_tree.py n rho k probes [tol]
"""
import sys, math, time
import numpy as np
import ringbb2 as F


def main():
    n = int(sys.argv[1]); rho = float(sys.argv[2]); k = int(sys.argv[3]); probes = int(sys.argv[4])
    tol = float(sys.argv[5]) if len(sys.argv) > 5 else 0.02
    delta = 2 * math.asin(1 / rho); RI = math.sqrt(rho * rho - 4)
    roots = F.presplit(n, k, rho, 4096)
    rng = np.random.default_rng(1)
    est = []
    t0 = time.time()
    for p in range(probes):
        b = roots[rng.integers(len(roots))].copy()
        weight = float(len(roots)); total = weight
        depth = 0
        while True:
            r = F.box_ok(b[0:k], b[k:2 * k], b[2 * k:3 * k], b[3 * k:4 * k], k, n, rho, delta, RI, F.RHO_M, False)
            if r > 0:
                break
            slo = b[0:k]; shi = b[k:2 * k]; plo = b[2 * k:3 * k]; phi = b[3 * k:4 * k]
            j, c, w = F.choose_split(slo, shi, plo, phi, k)
            if w < tol:
                break
            b1, b2 = F.split_box(b, k)
            b = b1 if rng.random() < 0.5 else b2
            weight *= 2.0; total += weight; depth += 1
            if depth > 400:
                break
        est.append(total)
    est = np.array(est)
    m = est.mean(); se = est.std() / math.sqrt(len(est))
    print(f"n={n} k={k} rho={rho}: estimated nodes {m:.3e} (+- {se:.1e}, {probes} probes, {time.time()-t0:.1f}s)  median {np.median(est):.2e} max {est.max():.2e}")


if __name__ == "__main__":
    main()
