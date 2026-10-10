# brute-force test of bmax_arcs: discretize circle finely and do exact DP/greedy over fine grid
import numpy as np, math
from ringbb import bmax_arcs, TWO_PI
rng = np.random.default_rng(1)
def brute(arcs, delta, M=20000):
    # allowed grid points
    xs = np.arange(M) * TWO_PI / M
    allowed = np.ones(M, bool)
    for lo, hi in arcs:
        for lift in (-TWO_PI, 0, TWO_PI):
            allowed &= ~((xs > lo + lift) & (xs < hi + lift))
    A = xs[allowed]
    if len(A) == 0: return 0
    best = 0
    # greedy from each allowed grid point among a subsample (arc starts are what matter; brute over all starts is slow -> subsample + starts)
    starts = A[::max(1, len(A)//400)]
    for x0 in starts:
        cnt = 1; x = x0; lim = x0 + TWO_PI - delta
        AA = np.concatenate([A, A + TWO_PI])
        while True:
            j = np.searchsorted(AA, x + delta - 1e-12)
            if j >= len(AA) or AA[j] > lim + 1e-9: break
            x = AA[j]; cnt += 1
        best = max(best, cnt)
    return best
bad = 0
for trial in range(300):
    m = rng.integers(0, 7)
    delta = rng.uniform(0.3, 1.2)
    arcs = []
    for i in range(m):
        lo = rng.uniform(0, TWO_PI); w = rng.uniform(0.01, 1.5)
        arcs.append((lo, lo + w))
    a_lo = np.array([a for a, b in arcs] + [0.0]); a_hi = np.array([b for a, b in arcs] + [0.0])
    v = bmax_arcs(a_lo, a_hi, m, delta)
    b = brute(arcs, delta)
    if v < b or v > b + 1:   # grid brute is a lower bound (discretization); allow v >= b, flag if v < b
        bad += 1
        print("MISMATCH", m, delta, arcs, v, b)
print("done, bad =", bad)
