"""Empirical accuracy of the float64 elementary functions used inside the numba kernels
(cos, asin, sqrt, floor-based reduction) against arb, on the argument ranges that occur.
Supports the claim that float errors are many orders of magnitude below the 1e-9 margins
of the float B&B (the arb B&B does not depend on this at all)."""
import math, time
import numpy as np
from numba import njit
from flint import arb, ctx

ctx.prec = 120


@njit(cache=True)
def f_cos(x):
    return math.cos(x)


@njit(cache=True)
def f_asin(x):
    return math.asin(x)


@njit(cache=True)
def f_sqrt(x):
    return math.sqrt(x)


def ulp_err(f, exact):
    e = float(abs(arb(f) - exact).upper())
    u = np.spacing(abs(f)) if f != 0 else 5e-324
    return e / u, e


rng = np.random.default_rng(1)
N = 200000
worst = {}
t0 = time.time()
for name, fn, gen, ex in [
        ("cos", f_cos, lambda: rng.uniform(-14.0, 14.0), lambda x: arb(x).cos()),
        ("asin", f_asin, lambda: rng.uniform(0.0, 1.0) ** 3, lambda x: arb(x).asin()),
        ("sqrt", f_sqrt, lambda: rng.uniform(0.0, 1.0) ** 3, lambda x: arb(x).sqrt())]:
    wu = 0.0
    wa = 0.0
    for t in range(N):
        x = gen()
        f = fn(x)
        u, a = ulp_err(f, ex(x))
        wu = max(wu, u)
        wa = max(wa, a)
    worst[name] = (wu, wa)
    print(f"{name:5s}: max error {wu:.3f} ulp, max abs error {wa:.3e}  ({N} samples)")
print("time %.1fs" % (time.time() - t0))
