"""
Parallel driver (<= 4 worker processes) for the B&B of bnb2.py.

usage: python run_bnb.py RHO K [--tol T] [--accept-pentagon EPS] [--workers 4]
                         [--budget NODES_PER_TASK] [--out results_k.json]

Result: number of nodes, prune statistics, completed volume (must be 1.0), the list of
unresolved boxes (reached tolerance without being pruned / accepted) and, with
--accept-pentagon, the accepted boxes (all contained in the EPS-neighbourhood of the
regular pentagon of circumradius 1/sin 36 deg).
"""
import sys, os, json, math, time, argparse
os.environ.setdefault("NUMBA_NUM_THREADS", "1")
import numpy as np
from multiprocessing import Pool
from core import constants, EPS_DB, excess_slack
import bnb2 as BB

G = {}


def init_worker(cfg):
    G.update(cfg)
    # warm up compilation
    k = cfg["k"]
    B = BB.root_box2(k, cfg["RI_hi"], cfg["rm"])[None].copy()
    surv = np.zeros((1, k, 4))
    stats = np.zeros(BB.NSTAT, dtype=np.int64)
    BB.dfs2(B, np.ones(1), k, cfg["m"], cfg["rho"], cfg["rho_m2"], cfg["db_lo"], cfg["db_hi"],
            cfg["slack_hi"], cfg["rm"], cfg["tol"], 1, surv, stats, cfg["accept"], cfg["pent"],
            1 << 62, cfg["sym"])


def task(args):
    boxes, vols = args
    k = G["k"]
    surv = np.zeros((G["maxsurv"], k, 4))
    stats = np.zeros(BB.NSTAT, dtype=np.int64)
    t0 = time.time()
    nodes, nsurv, done, rest, rvol = BB.dfs2(
        np.array(boxes), np.array(vols), k, G["m"], G["rho"], G["rho_m2"], G["db_lo"],
        G["db_hi"], G["slack_hi"], G["rm"], G["tol"], G["budget"], surv, stats, G["accept"],
        G["pent"], 1 << 62, G["sym"])
    return dict(nodes=int(nodes), nsurv=int(nsurv), done=float(done), stats=stats.tolist(),
                surv=surv[:min(nsurv, G["maxsurv"])].tolist(), rest=rest.tolist(),
                rvol=rvol.tolist(), time=time.time() - t0)


def split_root(k, RI_hi, cfg, n_target):
    """Breadth-first expansion of the root (in the main process) to n_target boxes."""
    from collections import deque
    arc_a = np.empty(k + 2); arc_b = np.empty(k + 2); W = np.empty((8, k + 4))
    q = deque([(BB.root_box2(k, RI_hi, cfg["rm"]), 1.0)])
    stats = np.zeros(BB.NSTAT, dtype=np.int64)
    done = 0.0
    nodes = 0
    out = []
    while q and len(q) + len(out) < n_target:
        B, v = q.popleft()
        B = B.copy()
        nodes += 1
        code = BB.check_node2(B, k, cfg["m"], cfg["rho"], cfg["rho_m2"], cfg["db_lo"],
                              cfg["db_hi"], cfg["slack_hi"], cfg["rm"], arc_a, arc_b, W,
                              cfg["sym"])
        stats[code] += 1
        if code != BB.C_ALIVE:
            done += v
            continue
        best, bi, bd = BB.choose_split(B, k)
        if best < cfg["tol"]:
            out.append((B, v))
            continue
        mid = 0.5 * (B[bi, bd] + B[bi, bd + 1])
        B1 = B.copy(); B1[bi, bd + 1] = mid
        B2 = B.copy(); B2[bi, bd] = mid
        q.append((B1, 0.5 * v)); q.append((B2, 0.5 * v))
    out.extend(list(q))
    return out, done, nodes, stats


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("rho", type=float)
    ap.add_argument("k", type=int)
    ap.add_argument("--tol", type=float, default=1e-4)
    ap.add_argument("--accept-pentagon", type=float, default=0.0)
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--budget", type=float, default=2e6)
    ap.add_argument("--maxsurv", type=int, default=20000)
    ap.add_argument("--ntasks", type=int, default=256)
    ap.add_argument("--out", type=str, default="")
    ap.add_argument("--keep-surv", type=int, default=200000)
    ap.add_argument("--no-rm", action="store_true",
                    help="do not use the r_n bounds of F4 (counting rule, s_0 >= r_k)")
    ap.add_argument("--sym", type=int, default=0,
                    help="0: full symmetry breaking; 1: only rotation (no ordering/reflection)")
    a = ap.parse_args()
    
    rho, k = a.rho, a.k
    m = 15 - k
    RI_hi, db_lo, rho_m2 = constants(rho)
    cfg = dict(k=k, m=m, rho=rho, RI_hi=RI_hi, db_lo=db_lo, db_hi=db_lo + 2 * EPS_DB,
               rho_m2=rho_m2, slack_hi=excess_slack(rho, m, db_lo), tol=a.tol,
               budget=int(a.budget), maxsurv=a.maxsurv,
               accept=1 if a.accept_pentagon > 0 else 0,
               pent=np.array([1.0 / math.sin(math.pi / 5), a.accept_pentagon, 0.0]),
               rm=(np.zeros_like(BB.R_M) if a.no_rm else BB.R_M.copy()), sym=a.sym)
    t0 = time.time()
    init_worker(cfg)
    tasks, done0, nodes0, stats0 = split_root(k, RI_hi, cfg, a.ntasks)
    total_nodes = nodes0
    stats = stats0.astype(np.int64)
    done = done0
    surv_all = []
    nsurv_total = 0
    pending = [([B.tolist()], [v]) for B, v in tasks]
    rounds = 0
    with Pool(a.workers, initializer=init_worker, initargs=(cfg,)) as pool:
        while pending:
            rounds += 1
            new_pending = []
            for r in pool.imap_unordered(task, pending):
                total_nodes += r["nodes"]
                stats += np.array(r["stats"], dtype=np.int64)
                done += r["done"]
                nsurv_total += r["nsurv"]
                if len(surv_all) < a.keep_surv:
                    surv_all.extend(r["surv"])
                if r["rest"]:
                    rest, rvol = r["rest"], r["rvol"]
                    # re-split the remaining stack into several tasks
                    nch = max(1, min(16, len(rest) // 4))
                    for c in range(nch):
                        new_pending.append((rest[c::nch], rvol[c::nch]))
            pending = new_pending
            el = time.time() - t0
            print(f"[round {rounds}] nodes={total_nodes:.4g} done_volume={done:.9f} "
                  f"survivors={nsurv_total} pending_tasks={len(pending)} elapsed={el:.0f}s",
                  flush=True)
    el = time.time() - t0
    names = ["alive", "order", "dist", "ang", "rad", "excess", "cap", "accept", "-", "tol"]
    res = dict(rho=rho, k=k, m=m, tol=a.tol, accept_pentagon=a.accept_pentagon,
               use_F4=not a.no_rm, sym=a.sym, excess_rule=bool(cfg["slack_hi"] < 1e299),
               nodes=int(total_nodes), done_volume=done, survivors=nsurv_total,
               accepted=int(stats[BB.C_ACCEPT]), unresolved=int(stats[9]),
               stats={n: int(s) for n, s in zip(names, stats)}, time_s=el)
    print(json.dumps(res, indent=1))
    if a.out:
        res["survivor_boxes"] = surv_all
        json.dump(res, open(a.out, "w"))


if __name__ == "__main__":
    main()
