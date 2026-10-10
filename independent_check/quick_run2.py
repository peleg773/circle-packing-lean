"""Quick single-process exploration run of bnb2 (timing / tuning)."""
import sys, time, math
import numpy as np
from core import constants, EPS_DB, excess_slack
import bnb2 as BB

rho = float(sys.argv[1])
k = int(sys.argv[2])
budget = int(float(sys.argv[3]))
tol = float(sys.argv[4]) if len(sys.argv) > 4 else 1e-4
m = 15 - k
RI_hi, db_lo, rho_m2 = constants(rho)
db_hi = db_lo + 2 * EPS_DB
slack_hi = excess_slack(rho, m, db_lo)
root = BB.root_box2(k, RI_hi)[None].copy()
vol = np.ones(1)
surv = np.zeros((1000, k, 4))
stats = np.zeros(BB.NSTAT, dtype=np.int64)
pent = np.array([1.0 / math.sin(math.pi / 5), 1e-3, 0.0])
t0 = time.time()
nodes, nsurv, done, rest, rvol = BB.dfs2(root, vol, k, m, rho, rho_m2, db_lo, db_hi, slack_hi,
                                         BB.R_M, tol, budget, surv, stats, 0, pent)
dt = time.time() - t0
print(f"rho={rho} k={k} m={m}: nodes={nodes} survivors={nsurv} remaining={rest.shape[0]} "
      f"done_volume={done:.6g} time={dt:.1f}s rate={nodes/dt:.3g}/s")
print("stats [alive, order, dist, ang, rad, excess, cap, accept, -, tol]:", stats.tolist())
if done > 0:
    print("naive extrapolated total nodes ~ %.3g" % (nodes / done))
if nsurv:
    for b in surv[:min(nsurv, 3)]:
        print(np.array2string(b, precision=5))
