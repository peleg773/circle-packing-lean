"""Self-contained (literature-free) lower bounds  rho_m >= L_m  for m = 8..mmax, proved with the SAME rigorous
interior B&B (ringbb_rig_fast) at rho_test = L_m, using only
  * elementary bounds for m <= 7:  rho_m >= 1/sin(pi/m) (m <= 6), rho_7 >= rho_6 = 2
    (proof: for rho < 2 the push-out lemma moves every centre to the boundary circle -- a centre at the origin
     would force all others to |c| >= 2 > rho -- so m * 2 asin(1/rho) <= 2 pi);
  * bounds L_{m'} for m' < m proved earlier in this script.
If the B&B finds NO surviving box for every k in [kmin, kmax] at rho_test = L_m, then no configuration of m unit
circles fits in a container of radius L_m + 1 (monotonicity), i.e. rho_m > L_m.
The proven table is written to known_packings/proven_radius_bounds.json.

Usage: python prove_radius_bounds.py mmax [rel_margin]
"""
import sys, os, json, math, time
import numpy as np
from flint import arb, ctx
import ringbb_final as RB

HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(HERE)
OUTF = os.path.join(ROOT, "known_packings", "proven_radius_bounds.json")
ctx.prec = 200

# approximate known optima (used only to choose the TARGET L_m; the proof does not rely on them)
RHO_APPROX = {8: 2.3047648709624865, 9: 2.6131259297527530, 10: 2.8130256313981244, 11: 2.9238044001630872,
              12: 3.0296019301161835, 13: 3.2360679774997897, 14: 3.3284285548608367}


def br_lo(x):
    lo = float(x.mid())
    xl = x.mid() - x.rad()
    while arb(lo) > xl:
        lo = math.nextafter(lo, -math.inf)
    return math.nextafter(lo, -math.inf)


def elementary_table():
    pi = arb.pi()
    t = [0.0, 0.0] + [br_lo(1 / (pi / m).sin()) for m in range(2, 7)] + [2.0 - 1e-15]
    return t   # indices 0..7


def params_with_table(rho, table):
    R = arb(rho)
    dl = br_lo(2 * (1 / R).asin())
    x = 2 * (1 / R).asin(); dh = float(x.mid() + x.rad()); dh = math.nextafter(math.nextafter(dh, math.inf), math.inf)
    y = (R * R - 4).sqrt(); rih = float(y.mid() + y.rad()); rih = math.nextafter(math.nextafter(rih, math.inf), math.inf)
    rm = np.zeros(40)
    for i, v in enumerate(table):
        rm[i] = v
    # beyond the table: monotone extension (rho_m >= rho_{m-1}) -- valid lower bounds
    for i in range(len(table), 40):
        rm[i] = rm[i - 1]
    return dl, dh, rih, rm


def solve_k_table(n, k, rho, P, tol, nworkers=19, target=2000):
    from multiprocessing import Pool
    boxes = RB.presplit(n, k, rho, P, target)
    with Pool(nworkers) as pool:
        res = pool.map(RB._worker, [(n, k, rho, P, tol, int(1e12), b) for b in boxes], chunksize=1)
    nproc = sum(r[0] for r in res); reasons = sum(r[1] for r in res)
    nsurv = sum(len(r[2]) for r in res); unf = sum(1 for r in res if r[3] > 0)
    return nproc, reasons, nsurv, unf, len(boxes)


def main():
    mmax = int(sys.argv[1]); rel = float(sys.argv[2]) if len(sys.argv) > 2 else 1e-6
    table = elementary_table()
    proven = {}
    for m in range(8, mmax + 1):
        L = math.nextafter(RHO_APPROX[m] * (1 - rel), -math.inf)
        P = params_with_table(L, table)
        dl, dh, rih, rm = P
        from rigmath import TWO_PI_HI
        Bmax = math.floor(TWO_PI_HI / dl)          # rigorous upper bound on # boundary points
        kmin = max(0, m - Bmax)
        if kmin == 0:
            print(f"m={m}: all {m} points can lie on the boundary at L_m -> cannot prove (choose smaller L)")
            break
        # kmax: largest j with table lower bound <= R_I (j+1 points cannot fit if rm[j+1] > rih)
        kmax = 0
        while kmax + 1 <= m and rm[kmax + 1] <= rih:
            kmax += 1
        t0 = time.time()
        ok = True
        log = []
        for k in range(kmin, kmax + 1):
            nproc, reasons, nsurv, unf, nb0 = solve_k_table(m, k, L, P, 1e-7)
            log.append((k, nproc, int(nsurv), int(unf)))
            if nsurv > 0 or unf > 0:
                ok = False
        print(f"m={m}: L_m={L!r}  k in [{kmin},{kmax}]  results={log}  -> {'PROVED rho_m > L_m' if ok else 'NOT PROVED'}  ({time.time()-t0:.1f}s)", flush=True)
        if not ok:
            break
        proven[m] = L
        while len(table) <= m:
            table.append(table[-1])
        table[m] = L
    json.dump(dict(elementary=elementary_table(), proven=proven, rel_margin=rel), open(OUTF, "w"), indent=1)
    print("written", OUTF)


if __name__ == "__main__":
    main()
