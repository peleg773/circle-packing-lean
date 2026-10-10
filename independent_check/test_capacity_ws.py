"""capacity_ws (allocation-free, used in the B&B) must agree with capacity_ub (tested
against an independent slow implementation in test_primitives.py)."""
import random, math
import numpy as np
from core import capacity_ub, capacity_ws, constants, TWO_PI
rng = random.Random(99)
_, db, _ = constants(3.52135696470617)
W = np.empty((8, 16))
bad = 0
for t in range(200000):
    n = rng.randint(0, 11)
    a = np.empty(13); b = np.empty(13)
    for i in range(n):
        c = rng.uniform(-1, 7.5); h = rng.choice([rng.uniform(0.001, 0.7), rng.uniform(0.25, 0.35)])
        a[i] = c - h; b[i] = c + h
    need = rng.randint(1, 11)
    u1 = capacity_ub(a, b, n, db, need)
    u2 = capacity_ws(a, b, n, db, need, W)
    if (u1 >= need) != (u2 >= need) or (u1 < need and u1 != u2):
        bad += 1
print("capacity_ws vs capacity_ub: mismatches", bad, "of 200000")
