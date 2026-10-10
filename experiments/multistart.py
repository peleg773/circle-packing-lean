"""Multistart search for n points in the unit disk maximising the minimum distance.

Usage: python multistart.py n nstarts seed [strategy]
strategy in {uniform, ring, perturb, mixed}
Writes experiments/out/ms_n{n}_seed{seed}_{strategy}.json with all local optima found
(sorted), and prints a summary of distinct local optima (d, #boundary, #contacts, WL-hash).
NOT rigorous: floating point exploration only.
"""
import sys, os, json, time
import numpy as np
from multiprocessing import Pool
from search_lib import *

HERE = os.path.dirname(os.path.abspath(__file__))
OUTDIR = os.path.join(HERE, "out")
os.makedirs(OUTDIR, exist_ok=True)

BEST = {13: 0.6180339887498948, 14: 0.6008841611093620, 15: 0.5679628677369515,
        16: 0.5531852191443445, 17: 0.5274214663545747, 18: 0.5176380902050415,
        19: 0.5176380902050415, 20: 0.4851636074925118, 12: 0.6601287, 11: 0.6840402866513375,
        10: 0.7110, 9: 0.7653668647301796, 8: 0.8677674782351162}


def known_points(n):
    path = os.path.join(os.path.dirname(HERE), "known_packings", "known_packings_13_20.json")
    with open(path) as f:
        data = json.load(f)
    return np.array([[float(a), float(b)] for a, b in data[str(n)]["points"]])


def one_start(args):
    n, seed, strategy = args
    rng = np.random.default_rng(seed)
    dstar = BEST[n]
    if strategy == "mixed":
        strategy = rng.choice(["uniform", "ring", "perturb"], p=[0.5, 0.35, 0.15])
    if strategy == "uniform":
        P = random_disk(n, rng)
    elif strategy == "ring":
        k = rng.integers(max(3, n // 2), n)
        th = np.sort(rng.random(k)) * 2 * np.pi
        Pb = np.stack([np.cos(th), np.sin(th)], 1)
        Pi = random_disk(n - k, rng) * rng.uniform(0.4, 0.8)
        P = np.concatenate([Pb, Pi])
    elif strategy == "perturb":
        P = known_points(n)
        sc = rng.choice([0.02, 0.05, 0.1, 0.2])
        P = P + rng.normal(scale=sc, size=P.shape)
        # random symmetry-breaking: swap a point to a random location sometimes
        if rng.random() < 0.5:
            i = rng.integers(n)
            P[i] = random_disk(1, rng)[0]
    else:
        raise ValueError(strategy)
    # continuation on target separation
    for frac in (0.85, 0.95, 1.0):
        P, E = penalty_minimize(P, dstar * frac)
    P, d = polish_maxmin(P)
    P, d = polish_maxmin(P)
    bnd, con = contact_structure(P, d, tol=1e-6)
    sig = graph_signature(n, bnd, con)
    return dict(seed=int(seed), strategy=str(strategy), d=float(d), nb=len(bnd), nc=len(con), sig=sig,
                P=P.tolist())


def main():
    n = int(sys.argv[1]); N = int(sys.argv[2]); seed0 = int(sys.argv[3])
    strategy = sys.argv[4] if len(sys.argv) > 4 else "mixed"
    t0 = time.time()
    tasks = [(n, seed0 * 1000003 + k, strategy) for k in range(N)]
    with Pool(18) as pool:
        results = pool.map(one_start, tasks, chunksize=8)
    results.sort(key=lambda r: -r["d"])
    dstar = BEST[n]
    # cluster
    clusters = {}
    for r in results:
        key = (round(r["d"], 7), r["nb"], r["nc"], r["sig"])
        clusters.setdefault(key, []).append(r)
    keys = sorted(clusters, key=lambda k: -k[0])
    print(f"n={n} starts={N} seed0={seed0} strategy={strategy} time={time.time()-t0:.1f}s  best-known d*={dstar:.13f}")
    print(f"best found d={results[0]['d']:.15f}  (d - d*) = {results[0]['d'] - dstar:.3e}")
    for k in keys[:25]:
        print(f"  d={k[0]:.7f} (d/d*-1={k[0]/dstar-1:+.2e})  boundary={k[1]:2d} contacts={k[2]:2d} hits={len(clusters[k]):5d}  sig={k[3][:10]}")
    out = dict(n=n, N=N, seed0=seed0, strategy=strategy, dstar=dstar,
               clusters=[dict(d=k[0], nb=k[1], nc=k[2], sig=k[3], hits=len(clusters[k]),
                              example=clusters[k][0]) for k in keys])
    with open(os.path.join(OUTDIR, f"ms_n{n}_seed{seed0}_{strategy}.json"), "w") as f:
        json.dump(out, f)


if __name__ == "__main__":
    main()
