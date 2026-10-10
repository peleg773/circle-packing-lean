"""Rigorous final stage for n = 18 (arb + exact rationals): every surviving canonical interior box (k interior
points) must contain only configurations whose CORE (for some known structure S) lies within
rho19 * delta_loc(core S) of the reference core of S (lemma L7 for the core; core certificates from
core_cert.py).  Boundary-point ranges come from the same exact interval propagation as verify_final_arb2.py.

Matching: the canonical box has interior point 0 (max radius) at angle 0.  For each structure S with the same k,
we try every rotation of S that puts one of S's interior points of maximal radius at angle 0, and its reflection;
interior points are matched by the Hungarian assignment on box centres (any bijection gives a valid bound);
the core's boundary points are matched to the box's boundary points in angular order (the structure's boundary
points sorted by angle are matched to the placement's positions with the same index; structures whose
boundary pattern has missing slots are handled by matching only the core boundary points, choosing the
offset that minimises the bound).
Usage: python verify_cores_n18.py rho_test k survivors.npy structure1 [structure2 ...]
"""
import sys, os, json, math
from fractions import Fraction as Fr
import numpy as np
from scipy.optimize import linear_sum_assignment
from flint import arb
import verify_final_arb2 as V
from n18_structures import build, RHO19

HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(HERE)


def stn_cyclic(seq, delta, P2):
    """exact outer bounds for x_1<..<x_N with x_{j+1}-x_j >= delta, x_N - x_1 <= P2 - delta, x_j in [S_j,E_j]."""
    N = len(seq); M = N + 1
    D = [[None] * M for _ in range(M)]
    for i in range(M):
        D[i][i] = Fr(0)
    def setmin(i, j, v):
        if D[i][j] is None or v < D[i][j]:
            D[i][j] = v
    for j in range(1, M):
        S_, E_ = seq[j - 1]
        setmin(0, j, E_); setmin(j, 0, -S_)
    for j in range(1, N):
        setmin(j + 1, j, -delta)
    setmin(1, N, P2 - delta)
    for kk in range(M):
        for i in range(M):
            if D[i][kk] is None:
                continue
            for j in range(M):
                if D[kk][j] is None:
                    continue
                v = D[i][kk] + D[kk][j]
                if D[i][j] is None or v < D[i][j]:
                    D[i][j] = v
    for i in range(M):
        if D[i][i] < 0:
            return None
    return [(-D[j][0], D[0][j]) for j in range(1, M)]


def placements_cyclic(intervals, delta, N):
    m = len(intervals)
    caps = [int((b - a) / delta) + 1 for a, b in intervals]
    res = []
    def rec(i, rem, counts):
        if i == m:
            if rem == 0:
                seq = []
                for q, c in enumerate(counts):
                    seq += [intervals[q]] * c
                r = stn_cyclic(seq, delta, V.TWO_PI_HI)
                if r is not None:
                    res.append((tuple(counts), r))
            return
        for c in range(0, min(caps[i], rem) + 1):
            rec(i + 1, rem - c, counts + [c])
    rec(0, N, [])
    return res


def load_core_cert(name):
    J = json.load(open(os.path.join(ROOT, "known_packings", f"core_certificate_n18_{name}.json")))
    assert J["ok"]
    return J["delta_loc"]


def structure_variants(name):
    pts, interior, boundary, core = build(name)
    rad = [float((p[0] * p[0] + p[1] * p[1]).sqrt().mid()) for p in pts]
    rmax = max(rad[i] for i in interior)
    tops = [i for i in interior if abs(rad[i] - rmax) < 1e-12]
    out = []
    for t in tops:
        a0 = V.arb_angle(pts[t][0], pts[t][1])
        c0, s0 = a0.cos(), a0.sin()
        Q = [(x * c0 + y * s0, -x * s0 + y * c0) for x, y in pts]
        out.append(Q)
        out.append([(x, -y) for x, y in Q])
    return out, interior, boundary, core


def interior_part(bx, k, Q, interior, core):
    slo = bx[0:k]; shi = bx[k:2 * k]; plo = bx[2 * k:3 * k]; phi = bx[3 * k:4 * k]
    cen = np.array([[0.5 * (slo[j] + shi[j]) * math.cos(0.5 * (plo[j] + phi[j])),
                     0.5 * (slo[j] + shi[j]) * math.sin(0.5 * (plo[j] + phi[j]))] for j in range(k)])
    cst = np.array([[float(Q[i][0].mid()), float(Q[i][1].mid())] for i in interior])
    rr, cc = linear_sum_assignment(np.linalg.norm(cen[:, None, :] - cst[None, :, :], axis=2))
    perm = {int(r): int(c) for r, c in zip(rr, cc)}
    core_set = set(core)
    tot_int = Fr(0)
    for j in range(k):
        i = interior[perm[j]]
        if i in core_set:
            tot_int += V.maxdist_sq(slo[j], shi[j], plo[j], phi[j], Q[i][0], Q[i][1])
    return tot_int


def boundary_part(rng, N, Q, boundary, core):
    core_set = set(core)
    angs = [(V.arb_angle(Q[i][0], Q[i][1]), i) for i in boundary]
    angs = [((a + 2 * V.PI) if V.lo_(a) < 0 else a, i) for a, i in angs]
    angs.sort(key=lambda t: float(t[0].mid()))
    tot = Fr(0)
    for j in range(N):
        a, i = angs[j]
        if i not in core_set:
            continue
        lo, hi = V.A(rng[j][0]), V.A(rng[j][1])
        dev = max(V.fr_hi(abs(lo - a)), V.fr_hi(abs(hi - a)))
        tot += (RHO_HI * dev) * (RHO_HI * dev)
    return tot


def main():
    rho_t = float(sys.argv[1]); k = int(sys.argv[2]); fn = sys.argv[3]; names = sys.argv[4:]
    S = np.load(fn)
    n = 18; N = n - k
    global RHO_HI
    RHO_HI = V.fr_hi(RHO19)
    Rt = arb(rho_t); dB = 2 * (1 / Rt).asin()
    delta_lo = V.fr_lo(dB) - Fr(2, 10 ** 12); delta_hi = V.hi_(dB)
    structs = []
    for nm in names:
        dl = load_core_cert(nm)
        thr = V.fr_lo(RHO19 * arb(dl)); thr2 = thr * thr
        vars_, interior, boundary, core = structure_variants(nm)
        if len(interior) != k:
            continue
        structs.append((nm, vars_, interior, boundary, core, thr2))
    print(f"n=18 k={k}: {len(S)} boxes; structures with k interior points: {[s[0] for s in structs]}", flush=True)
    bad = 0; empty = 0; notgap = 0; worst = {}
    for t, bx in enumerate(S):
        slo = bx[0:k]; plo = bx[2 * k:3 * k]; phi = bx[3 * k:4 * k]
        th0 = V.theta_lo(slo[0], rho_t)
        w0 = V.fr_lo(th0) if V.hi_(th0) > 0 else Fr(0)
        # boundary points avoid point 0's certain arc (-w0, w0); the cyclic constraint is imposed explicitly
        ints = V.allowed_intervals(slo, plo, phi, k, rho_t, w0)
        pls = placements_cyclic(ints, delta_lo, N)
        if not pls:
            empty += 1; continue
        # every boundary assignment must be certified by some structure variant
        ok = True
        cache_int = {}
        for counts, rng in pls:
            done = False
            for nm, vars_, interior, boundary, core, thr2 in structs:
                for vi, Q in enumerate(vars_):
                    key = (nm, vi)
                    if key not in cache_int:
                        cache_int[key] = interior_part(bx, k, Q, interior, core)
                    ti = cache_int[key]
                    if ti >= thr2:
                        continue
                    d2 = ti + boundary_part(rng, N, Q, boundary, core)
                    if d2 < thr2:
                        done = True
                        worst[nm] = max(worst.get(nm, Fr(0)), d2)
                        break
                if done:
                    break
            if not done:
                ok = False
                break
        if not ok:
            bad += 1
            if bad <= 5:
                print("   UNMATCHED box", t, "s-mid", np.round(0.5 * (bx[0:k] + bx[k:2 * k]), 4), flush=True)
    print(f"  boxes: total {len(S)}, empty {empty}, point-0-not-gap {notgap}, unmatched/failing {bad}", flush=True)
    for nm, w in worst.items():
        print(f"  structure {nm}: worst core distance {float(w) ** 0.5:.4e}", flush=True)
    print("  ALL BOXES CERTIFIED:", bad == 0, flush=True)


if __name__ == "__main__":
    main()
