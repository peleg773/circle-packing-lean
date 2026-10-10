"""Unit test for radial_forbidden: radii it excludes must really be infeasible."""
import math, random
import numpy as np
from core import radial_forbidden, cos_min_interval, TWO_PI
rng = random.Random(7)
bad = 0; nonempty = 0
for t in range(20000):
    sj0 = rng.uniform(0, 2.9); sj1 = min(2.9, sj0 + rng.uniform(0, 0.6))
    pi0 = rng.uniform(0, TWO_PI); pi1 = pi0 + rng.uniform(0, 0.8)
    pj0 = rng.uniform(0, TWO_PI); pj1 = pj0 + rng.uniform(0, 0.8)
    if rng.random() < 0.5:
        pj0 = pi0 + rng.uniform(-0.3, 0.3); pj1 = pj0 + rng.uniform(0, 0.3)
    cm = cos_min_interval(pi0 - pj1, pi1 - pj0)
    u, v = radial_forbidden(sj0, sj1, cm)
    if u >= v or v <= 0.0:
        continue
    nonempty += 1
    # sample s in (u,v); for all sampled (sj, psi_i, psi_j) the distance must be < 2
    for r in range(30):
        s = rng.uniform(max(u, 0), v)
        # worst case search: maximise distance over box j and angle of i
        best = 0
        for q in range(60):
            sj = rng.choice([sj0, sj1, rng.uniform(sj0, sj1)])
            a = rng.choice([pi0, pi1, rng.uniform(pi0, pi1)])
            b = rng.choice([pj0, pj1, rng.uniform(pj0, pj1)])
            d2 = s*s + sj*sj - 2*s*sj*math.cos(a-b)
            best = max(best, d2)
        if best >= 4.0:
            bad += 1
print("nonempty forbidden intervals:", nonempty, " violations:", bad)
assert bad == 0
