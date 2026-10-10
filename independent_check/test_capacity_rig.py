"""capacity_rig (exact rational greedy used by the arb B&B) vs capacity_ub (float)."""
import random, math
import numpy as np
from core import capacity_ub
from arb_bnb import Ctx, capacity_rig
rng = random.Random(5)
c = Ctx(3.52135696470617, 6)
db = float(c.db_q)
bad = 0; N = 20000
for t in range(N):
    n = rng.randint(0, 9)
    arcs = []
    for i in range(n):
        cc = rng.uniform(-1, 7.5); h = rng.choice([rng.uniform(0.001, 0.7), rng.uniform(0.25, 0.35)])
        arcs.append((cc - h, cc + h))
    need = rng.randint(1, 11)
    a = np.array([x[0] for x in arcs] + [0.0]); b = np.array([x[1] for x in arcs] + [0.0])
    u1 = capacity_ub(a, b, n, db, need)
    u2 = capacity_rig(c, arcs, need)
    if (u1 >= need) != (u2 >= need):
        bad += 1
        if bad < 5: print("mismatch", u1, u2, need, arcs)
print("capacity_rig vs capacity_ub: decision mismatches", bad, "of", N)
