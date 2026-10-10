import numpy as np, mpmath as mp
from rigmath import *
mp.mp.dps = 40
rng = np.random.default_rng(5)
bad = 0; worst_w = 0
for c in np.concatenate([rng.uniform(-1, 1, 20000), [0.0, 1.0, -1.0, 0.5, -0.5, 1e-300, -1e-300, 0.9999999999, -0.9999999999]]):
    c = float(c)
    lo, hi = acos_lo(c), acos_hi(c)
    ex = mp.acos(mp.mpf(c))
    if not (mp.mpf(lo) <= ex <= mp.mpf(hi)): bad += 1; print("ACOS FAIL", c, lo, hi, ex)
    worst_w = max(worst_w, hi - lo)
print("acos: bad", bad, "max width", worst_w)
bad = 0; worst_w = 0
for x in np.concatenate([rng.uniform(-40, 40, 20000), [0.0, np.pi, -np.pi, 2*np.pi, 3*np.pi, 1e-300]]):
    x = float(x)
    lo, hi = cos_interval_pt(x)
    ex = mp.cos(mp.mpf(x))
    if not (mp.mpf(lo) <= ex <= mp.mpf(hi)): bad += 1; print("COS FAIL", x, lo, hi, ex)
    worst_w = max(worst_w, hi - lo)
print("cos: bad", bad, "max width", worst_w)
bad = 0
for t in range(20000):
    a = float(rng.uniform(-10, 10)); w = float(rng.uniform(0, 5))
    b = a + w
    lo = cos_min_lo(a, b)
    # exact min of cos on [a,b]
    xs = [mp.mpf(a), mp.mpf(b)]
    k0 = int(mp.floor((mp.mpf(a) - mp.pi) / (2*mp.pi))) - 1
    for k in range(k0, k0 + 5):
        z = mp.pi + 2*mp.pi*k
        if mp.mpf(a) <= z <= mp.mpf(b): xs.append(z)
    ex = min(mp.cos(z) for z in xs)
    if not (mp.mpf(lo) <= ex): bad += 1; print("COSMIN FAIL", a, b, lo, ex)
print("cos_min_lo: bad", bad)
