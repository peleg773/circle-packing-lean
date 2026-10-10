"""Quick single-process exploration run (for timing / tuning)."""
import sys, time
import numpy as np
from core import constants
import bnb as BB

rho = float(sys.argv[1])
k = int(sys.argv[2])
budget = int(float(sys.argv[3]))
tol = float(sys.argv[4]) if len(sys.argv) > 4 else 1e-4
m = 15 - k
RI_hi, db, rho_m2 = constants(rho)
root = BB.root_box(k, RI_hi)[None].copy()
surv = np.zeros((1000, k, 4))
stats = np.zeros(8, dtype=np.int64)
t0 = time.time()
nodes, nsurv, rest = BB.dfs(root, k, m, rho, rho_m2, db, tol, budget, surv, stats)
dt = time.time() - t0
print(f"rho={rho} k={k} m={m}: nodes={nodes} survivors={nsurv} remaining_stack={rest.shape[0]} "
      f"time={dt:.1f}s  rate={nodes/dt:.3g}/s")
print("stats [alive, order, dist, ang, cap, accept, -, overflow]:", stats.tolist())
if nsurv:
    for b in surv[:min(nsurv, 3)]:
        print(np.array2string(b, precision=5))
