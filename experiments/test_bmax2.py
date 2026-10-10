# Validate 'first point at an allowed-arc start suffices': compare bmax_arcs with max over many start points x0
# of the exact continuous greedy (greedy is optimal for a fixed first point).
import numpy as np, math
from ringbb import bmax_arcs, TWO_PI
rng = np.random.default_rng(2)
def allowed_intervals(arcs):
    # returns sorted list of closed allowed intervals on [0, 2pi) lifted to 3 periods
    M = 200000
    pts = []
    # build via exact complement on [0,2pi)
    segs = []
    for lo, hi in arcs:
        for lift in (-TWO_PI, 0, TWO_PI):
            segs.append((lo + lift, hi + lift))
    segs.sort()
    merged = []
    for a, b in segs:
        if merged and a < merged[-1][1]:
            merged[-1][1] = max(merged[-1][1], b)
        else:
            merged.append([a, b])
    allowed = []
    cur = -TWO_PI
    for a, b in merged:
        if a >= cur: allowed.append((cur, a))
        cur = max(cur, b)
    allowed.append((cur, 3 * TWO_PI))
    return allowed
def is_allowed(x, allowed):
    return any(a <= x <= b for a, b in allowed)
def next_allowed(x, allowed):
    best = None
    for a, b in allowed:
        if b < x: continue
        c = x if a <= x else a
        if best is None or c < best: best = c
    return best
def greedy(x0, allowed, delta):
    if not is_allowed(x0, allowed): return 0
    cnt = 1; x = x0; lim = x0 + TWO_PI - delta
    while True:
        p = next_allowed(x + delta, allowed)
        if p is None or p > lim: break
        x = p; cnt += 1
    return cnt
bad = 0
for trial in range(400):
    m = rng.integers(1, 7)
    delta = rng.uniform(0.25, 1.3)
    arcs = []
    for i in range(m):
        lo = rng.uniform(0, TWO_PI); w = rng.uniform(0.01, 1.2)
        arcs.append((lo, lo + w))
    a_lo = np.array([a for a, b in arcs]); a_hi = np.array([b for a, b in arcs])
    v = bmax_arcs(a_lo, a_hi, m, delta)
    al = allowed_intervals(arcs)
    xs = list(rng.uniform(0, TWO_PI, 600)) + [a for a, b in al if 0 <= a < TWO_PI] + [b for a,b in al if 0<=b<TWO_PI]
    g = max(greedy(x, al, delta) for x in xs)
    if v != g:
        bad += 1; print("MISMATCH", m, delta, arcs, v, g)
print("done, bad =", bad)
