"""Heuristic search (SLSQP, random starts) for the smallest rho admitting k interior +
(15-k) boundary centres.  Only used to produce explicit feasible configurations for
validating the B&B (an upper bound on the critical rho for each k)."""
import sys, json, math, time
import numpy as np
from multiprocessing import Pool
from configs import min_rho, unpack, check_config


def job(args):
    k, seed = args
    try:
        x, viol = min_rho(k, seed)
    except Exception as e:
        return (k, seed, None, None)
    return (k, seed, x.tolist(), viol)


if __name__ == "__main__":
    nstart = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    ks = [5, 6, 7, 8, 9, 10]
    jobs = [(k, s) for k in ks for s in range(nstart)]
    best = {}
    t0 = time.time()
    with Pool(4) as pool:
        for k, seed, x, viol in pool.imap_unordered(job, jobs, chunksize=2):
            if x is None or viol > 1e-9 or not (3.0 <= x[0] <= 5.0):
                continue
            x = np.array(x)
            rho, P, a = unpack(x, k, 15 - k)
            # make strictly feasible at a slightly larger rho
            r2 = rho + 1e-9
            if check_config(P, a, r2) < -1e-12:
                continue
            if k not in best or rho < best[k][0]:
                best[k] = (rho, x.tolist())
    print("time %.1fs" % (time.time() - t0))
    for k in ks:
        if k in best:
            print(k, "best rho found: %.10f" % best[k][0])
    json.dump({str(k): v for k, v in best.items()}, open("rho_crit_configs.json", "w"))
