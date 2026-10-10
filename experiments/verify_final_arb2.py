"""RIGOROUS final stage (arb balls + exact rationals; no floating-point decisions):
every surviving canonical interior box lies in the local-uniqueness neighbourhood of c*  (lemma L8).

Canonical form: interior point 0 (largest radius) has angle 0.  We REQUIRE (and check rigorously) that
point 0 is a gap point for the whole box: its certainly-forbidden half-width w0 satisfies 2*w0 >= delta_hi.
Then every boundary angle lies in the segment S = [w0, 2pi - w0] (no wrap-around), and the cyclic constraint
between the last and first boundary points is implied (a_1 + 2pi - a_N >= 2 w0 >= delta).

For each survivor box:
 1. certainly-forbidden open arcs of interior points 1..k-1 (arb lower bound of theta(s_lo), endpoints moved
    inward), together with their translates by +-2pi (translates additionally shrunk by 1e-12 to absorb the
    uncertainty of 2pi), intersected with S -> allowed closed intervals of S (exact rationals);
 2. all assignments of the N = n-k boundary points (in increasing angular order) to allowed intervals;
    exact forward/backward passes on the chain {a_{j+1} - a_j >= delta_lo, a_j in its interval}
    -> outer bounds [lo_j, hi_j] of every boundary angle (relaxed constraints => outer bounds are valid);
 3. D^2 = min over relabellings (interior permutations, reflection) of
          sum_int  max_{q in box_j} |q - c*_perm(j)|^2  +  max over assignments of
          sum_bnd (rho*_hi * max(|lo_j - a*_j|, |hi_j - a*_j|))^2
    (arb upper bounds; boundary points are at radius rho* exactly in the assembly argument);
 4. require D < rho*_lo * delta_loc_lo.
A box with no feasible assignment contains no configuration and is reported as empty; a box whose point 0
is not certified to be a gap point counts as FAILING (never skipped).
Usage: python verify_final_arb.py n rho_test k survivors.npy [json_out]
"""
import sys, os, json, math, itertools
from fractions import Fraction as Fr
import numpy as np
from flint import arb, ctx

ctx.prec = 200
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(HERE)
C = json.load(open(os.path.join(HERE, "rig_consts.json")))
TWO_PI_LO = Fr(C["consts"]["TWO_PI"][0]); TWO_PI_HI = Fr(C["consts"]["TWO_PI"][1])
PI = arb.pi()
SHRINK = Fr(1, 10 ** 12)


def lo_(x):
    return x.mid() - x.rad()


def hi_(x):
    return x.mid() + x.rad()


def fr_lo(x):   # exact rational <= every point of the arb ball x
    v = float(lo_(x)); v = math.nextafter(v, -math.inf)
    while arb(v) > lo_(x):
        v = math.nextafter(v, -math.inf)
    return Fr(v)


def fr_hi(x):
    v = float(hi_(x)); v = math.nextafter(v, math.inf)
    while arb(v) < hi_(x):
        v = math.nextafter(v, math.inf)
    return Fr(v)


def A(fr):      # exact rational -> arb (exact for dyadic rationals; otherwise a tight enclosure)
    return arb(fr.numerator) / arb(fr.denominator)


def arb_angle(x, y):
    if hi_(x) < 0:
        return PI + arb.atan2(-y, -x)
    return arb.atan2(y, x)


def load_cstar(n):
    with open(os.path.join(ROOT, "known_packings", f"local_certificate_n{n}.json")) as f:
        Cc = json.load(f)
    tm, tr = Cc["t_star_ball"].strip("[]").split("+/-")
    t = arb(tm.strip(), tr.strip())
    rho = 2 / t.sqrt()
    err = arb("1e-37")
    pts = [(arb(arb(a).mid(), err), arb(arb(b).mid(), err)) for a, b in Cc["points_mid"]]
    P = [(rho * x, rho * y) for x, y in pts]
    dm, dr = Cc["delta_loc"].strip("[]").split("+/-")
    dloc = arb(dm.strip()) - arb(dr.strip())
    return P, Cc["boundary"], rho, dloc


def theta_lo(s, rho):
    """arb ball whose LOWER end is a valid lower bound of theta_rho(s') for all s' in [s, R_I] (theta increasing)."""
    if s <= 0:
        return arb(0)
    S = arb(s); R = arb(rho)
    c = (S * S + R * R - 4) / (2 * S * R)
    ch = hi_(c)
    if ch >= 1:
        return arb(0)
    return arb(ch).acos()


def allowed_intervals(slo, plo, phi, k, rho, w0):
    """allowed closed intervals of the segment [w0, 2pi_hi - w0] (exact rationals)."""
    segL = w0; segR = TWO_PI_HI - w0
    forb = []
    for j in range(1, k):
        th = theta_lo(slo[j], rho)
        if hi_(th) <= 0:
            continue
        L = fr_hi(arb(phi[j]) - arb(lo_(th))) + SHRINK
        H = fr_lo(arb(plo[j]) + arb(lo_(th))) - SHRINK
        if H <= L:
            continue
        forb.append((L, H))
        forb.append((L + TWO_PI_HI + SHRINK, H + TWO_PI_LO - SHRINK))
        forb.append((L - TWO_PI_LO + SHRINK, H - TWO_PI_HI - SHRINK))
    forb.sort()
    merged = []
    for a, b in forb:
        if b <= a:
            continue
        if merged and a < merged[-1][1]:
            merged[-1][1] = max(merged[-1][1], b)
        else:
            merged.append([a, b])
    allowed = []
    cur = segL
    for a, b in merged:
        if b <= segL or a >= segR:
            continue
        if a >= cur:
            allowed.append((cur, min(a, segR)))
        cur = max(cur, b)
    if cur <= segR:
        allowed.append((cur, segR))
    return [(a, b) for a, b in allowed if a <= b]


def chain_bounds(seq, delta):
    """seq: list of (S,E) for points 1..N in increasing order; constraints x_{j+1}-x_j >= delta, x_j in [S_j,E_j].
    Exact outer bounds (earliest/latest positions) or None if infeasible."""
    N = len(seq)
    lo = [None] * N; hi = [None] * N
    lo[0] = seq[0][0]
    for j in range(1, N):
        lo[j] = max(seq[j][0], lo[j - 1] + delta)
    hi[N - 1] = seq[N - 1][1]
    for j in range(N - 2, -1, -1):
        hi[j] = min(seq[j][1], hi[j + 1] - delta)
    for j in range(N):
        if lo[j] > hi[j]:
            return None
    return list(zip(lo, hi))


def placements(intervals, delta, N):
    m = len(intervals)
    caps = [int((b - a) / delta) + 1 for a, b in intervals]
    res = []

    def rec(i, rem, counts):
        if i == m:
            if rem == 0:
                seq = []
                for q, c in enumerate(counts):
                    seq += [intervals[q]] * c
                r = chain_bounds(seq, delta)
                if r is not None:
                    res.append((tuple(counts), r))
            return
        for c in range(0, min(caps[i], rem) + 1):
            rec(i + 1, rem - c, counts + [c])
    rec(0, N, [])
    return res


def maxdist_sq(slo_, shi_, plo_, phi_, cx, cy):
    """arb upper bound of max over the polar box of |q - c|^2."""
    rc2 = cx * cx + cy * cy
    rc = rc2.sqrt()
    ac = arb_angle(cx, cy)
    lo = arb(plo_) - ac; hi = arb(phi_) - ac
    span_lo = lo_(lo); span_hi = hi_(hi)
    cm = None
    for m in range(-5, 6):
        z = (2 * m + 1) * PI
        if not (hi_(z) < span_lo or lo_(z) > span_hi):
            cm = arb(-1)
    if cm is None:
        cm = A(min(fr_lo(lo.cos()), fr_lo(hi.cos())))      # exact rational lower bound of min cos
    best = None
    for s in (slo_, shi_):
        S = arb(s)
        v = fr_hi(S * S + rc2 - 2 * S * rc * cm)            # exact rational upper bound
        best = v if best is None or v > best else best
    return best


def main():
    n = int(sys.argv[1]); rho_t = float(sys.argv[2]); k = int(sys.argv[3]); fn = sys.argv[4]
    jout = sys.argv[5] if len(sys.argv) > 5 else None
    S = np.load(fn)
    P, B, rho_s, dloc = load_cstar(n)
    N = n - k
    I = [i for i in range(n) if i not in B]
    rad = [(P[i][0] * P[i][0] + P[i][1] * P[i][1]).sqrt() for i in range(n)]
    Ii = sorted(I, key=lambda i: -float(rad[i].mid()))
    a0 = arb_angle(P[Ii[0]][0], P[Ii[0]][1])
    c0, s0 = a0.cos(), a0.sin()
    Q = [(x * c0 + y * s0, -x * s0 + y * c0) for x, y in P]
    variants = [Q, [(x, -y) for x, y in Q]]
    Rt = arb(rho_t)
    dB = 2 * (1 / Rt).asin()
    delta_lo = fr_lo(dB) - Fr(2, 10 ** 12)
    delta_hi = hi_(dB)
    thr = lo_(rho_s * dloc)
    THR = fr_lo(arb(thr)); THR2 = THR * THR          # exact rational lower bound of the threshold, squared
    RHO_HI = fr_hi(rho_s)
    print(f"n={n} k={k}: {len(S)} boxes; threshold rho* delta_loc >= {float(thr):.4e}", flush=True)
    worst2 = Fr(0); bad = 0; empty = 0; not_gap0 = 0
    for t, bx in enumerate(S):
        slo = bx[0:k]; shi = bx[k:2 * k]; plo = bx[2 * k:3 * k]; phi = bx[3 * k:4 * k]
        th0 = theta_lo(slo[0], rho_t)
        if not (2 * arb(lo_(th0)) >= arb(delta_hi)):
            not_gap0 += 1; bad += 1
            continue
        w0 = fr_lo(th0)
        ints = allowed_intervals(slo, plo, phi, k, rho_t, w0)
        pls = placements(ints, delta_lo, N)
        if not pls:
            empty += 1
            continue
        best_total2 = None                       # exact rational upper bound of D^2 for the best relabelling
        for V in variants:
            cint = [V[i] for i in Ii]
            best_int = None
            for perm in itertools.permutations(range(k)):
                tot = Fr(0)
                for j in range(k):
                    tot += maxdist_sq(slo[j], shi[j], plo[j], phi[j], *cint[perm[j]])
                if best_int is None or tot < best_int:
                    best_int = tot
            angs = [arb_angle(V[i][0], V[i][1]) for i in B]
            angs = [a + 2 * PI if lo_(a) < 0 else a for a in angs]       # all in (0, 2pi)
            angs = sorted(angs, key=lambda a: float(a.mid()))
            worst_b = Fr(0)
            for counts, rng in pls:
                tot = Fr(0)
                for j in range(N):
                    lo, hi = A(rng[j][0]), A(rng[j][1])
                    dev = max(fr_hi(abs(lo - angs[j])), fr_hi(abs(hi - angs[j])))
                    tot += (RHO_HI * dev) * (RHO_HI * dev)
                if tot > worst_b:
                    worst_b = tot
            total2 = best_int + worst_b
            if best_total2 is None or total2 < best_total2:
                best_total2 = total2
        if best_total2 > worst2:
            worst2 = best_total2
        if not (best_total2 < THR2):
            bad += 1
            if bad <= 5:
                print("   FAIL box", t, float(best_total2) ** 0.5, flush=True)
    ok = (bad == 0)
    print(f"  boxes: total {len(S)}, empty (no boundary placement) {empty}, point-0-not-gap {not_gap0}", flush=True)
    worstD = float(worst2) ** 0.5 * (1 + 1e-12)
    print(f"  worst D <= {worstD:.4e} < threshold {float(THR):.4e} ? {'YES' if ok else 'NO'};  failing boxes: {bad}  (decisions in exact rationals)", flush=True)
    if jout:
        json.dump(dict(n=n, k=k, rho_test=repr(rho_t), boxes=len(S), empty=empty, failing=bad,
                       worst_D_upper=worstD, threshold_lower=float(THR), ok=ok), open(jout, "w"), indent=1)


if __name__ == "__main__":
    main()
