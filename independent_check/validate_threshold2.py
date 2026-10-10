"""
k-range / threshold validation of the float B&B.

rho_c(k) = smallest radius found by the heuristic search (find_rho_crit.py), i.e. an
explicit configuration with k interior + (15-k) boundary centres exists for rho >= rho_c(k).

For every (rho, k) on a grid:
  * if rho >= rho_c(k): the B&B MUST leave a survivor (we stop at the first one);
  * if rho <  rho_c(k): we run the full B&B; an empty result shows the B&B proves
    infeasibility there (informative; survivors would mean a better configuration than the
    heuristic found, or insufficient resolution -- not a soundness problem).
Additionally rho_c(k) + 1e-7 for k = 6..10.
Runs at most 3 single-threaded jobs in parallel; node budget per job.
"""
import sys, json, math, time
import numpy as np
from multiprocessing import Pool
from core import constants, EPS_DB, excess_slack
import bnb2 as BB


def run(args):
    k, rho, stop_first, tol, budget = args
    m = 15 - k
    RI_hi, db_lo, rho_m2 = constants(rho)
    db_hi = db_lo + 2 * EPS_DB
    slack_hi = excess_slack(rho, m, db_lo)
    root = BB.root_box2(k, RI_hi)[None].copy()
    surv = np.zeros((10, k, 4))
    stats = np.zeros(BB.NSTAT, dtype=np.int64)
    pent = np.array([1.0, 0.0, 0.0])
    t0 = time.time()
    nodes, nsurv, done, rest, rvol = BB.dfs2(root, np.ones(1), k, m, rho, rho_m2, db_lo,
                                             db_hi, slack_hi, BB.R_M, tol, budget, surv,
                                             stats, 0, pent, 1 if stop_first else 1 << 62)
    return dict(k=k, rho=rho, expect_feasible=stop_first, tol=tol, nodes=int(nodes),
                survivors=int(nsurv), done_volume=float(done), unfinished=int(rest.shape[0]),
                excess_rule=bool(slack_hi < 1e299), time=time.time() - t0,
                first_survivor=surv[0].tolist() if nsurv else None)


if __name__ == "__main__":
    best = json.load(open("rho_crit_configs.json"))
    tol = 1e-3
    budget = int(float(sys.argv[1])) if len(sys.argv) > 1 else int(3e7)
    jobs = []
    for k in [6, 7, 8, 9, 10]:
        rc = best[str(k)][0]
        jobs.append((k, rc + 1e-7, True, tol, budget))
    for rho in [3.53, 3.56, 3.60, 3.65, 3.70, 3.75]:
        for k in [5, 6, 7, 8, 9, 10]:
            rc = best[str(k)][0]
            jobs.append((k, rho, rho >= rc, tol, budget))
    out = []
    with Pool(3) as pool:
        for r in pool.imap_unordered(run, jobs):
            r2 = {x: y for x, y in r.items() if x != "first_survivor"}
            print(json.dumps(r2), flush=True)
            out.append(r)
    json.dump(out, open("results/threshold_validation.json", "w"), indent=1)
