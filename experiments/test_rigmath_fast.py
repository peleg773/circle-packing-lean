import numpy as np, mpmath as mp
from rigmath_fast import acos_lo_fast
from rigmath import acos_lo
mp.mp.dps = 40
rng = np.random.default_rng(11)
xs = np.concatenate([rng.uniform(-1, 1, 200000), rng.uniform(0.9, 1, 50000), rng.uniform(-1, -0.9, 50000),
                     [0.0, -0.0, 1.0, -1.0, 1e-300, -1e-300, 0.5, -0.5, np.nextafter(1, 0), np.nextafter(-1, 0)]])
bad = 0; worst_loss = 0.0
for c in xs:
    c = float(c)
    lo = acos_lo_fast(c)
    ex = mp.acos(mp.mpf(c))
    if mp.mpf(lo) > ex:
        bad += 1; print("FAIL", c, lo, ex)
    worst_loss = max(worst_loss, float(ex) - lo)
print("acos_lo_fast: tests", len(xs), "bad", bad, "worst loss (rad)", worst_loss)
