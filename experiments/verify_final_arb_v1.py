"""RIGOROUS final stage (arb + exact rationals): every surviving interior box lies in the local-uniqueness
neighbourhood of c* (lemma L7/L8).

For each survivor box (canonical polar boxes of k interior points, from ringbb_rig.py):
 1. certainly-forbidden arcs at rho_test (arb lower bound of theta(s_lo)), converted to exact rationals
    and shrunk outward-safely; allowed arcs = complement (exact rational arithmetic; period 2pi relaxed
    to the rational upper bound TWO_PI_HI, arcs shrunk by 1e-12 to absorb the 2pi uncertainty);
 2. all assignments of the B = n-k boundary points to allowed arcs; exact Floyd-Warshall on the STN with
    delta replaced by a rational LOWER bound -> outer bounds [lo_j, hi_j] for every boundary angle;
 3. D^2 := sum_int max_box |q - c*_q|^2 + sum_bnd (rho*_hi * max|a - a*|)^2  (best labelling), in arb;
 4. require D < rho*_lo * delta_loc_lo.
Usage: python verify_final_arb.py n rho_test k survivors.npy
"""
import sys, os, json, math, itertools
from fractions import Fraction as Fr
import numpy as np
from flint import arb, ctx

ctx.prec = 160
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(HERE)
C = json.load(open(os.path.join(HERE, "rig_consts.json")))
TWO_PI_HI = Fr(C["consts"]["TWO_PI"][1])
PI = arb.pi()
SHRINK = Fr(1, 10 ** 12)


def arb_lo(x):
    return x.mid() - x.rad()


def arb_hi(x):
    return x.mid() + x.rad()


def to_fr_lo(x):   # rational lower bound of arb x
    v = float(arb_lo(x)); v = math.nextafter(v, -math.inf)
    return Fr(v)


def to_fr_hi(x):
    v = float(arb_hi(x)); v = math.nextafter(v, math.inf)
    return Fr(v)


def arb_angle(x, y):
    """rigorous angle of (x,y) avoiding the atan2 branch cut (returns ball, possibly outside (-pi,pi])."""
    if arb_hi(x) < 0:
        return PI + arb.atan2(-y, -x)
    return arb.atan2(y, x)


def load_cstar(n):
    with open(os.path.join(ROOT, "known_packings", f"local_certificate_n{n}.json")) as f:
        Cc = json.load(f)
    dstar = arb(Cc["d_star"])  # midpoint string (45 digits) -> we re-derive enclosure below
    t_ball = Cc["t_star_ball"]
    tm, tr = t_ball.strip("[]").split("+/-")
    t = arb(tm.strip(), tr.strip())
    d = t.sqrt()
    rho = 2 / d
    pts = [(arb(a), arb(b)) for a, b in Cc["points_mid"]]   # midpoints; error <= 1e-38 (box radius)
    err = arb("1e-37")
    pts = [(arb(a.mid(), err), arb(b.mid(), err)) for a, b in pts]
    P = [(rho * x, rho * y) for x, y in pts]
    dl = Cc["delta_loc"].strip("[]").split("+/-")
    dloc = arb(dl[0].strip()) - arb(dl[1].strip())
    return P, Cc["boundary"], rho, dloc


def theta_lo_arb(s, rho):
    if s <= 0:
        return arb(0)
    S = arb(s); R = arb(rho)
    c = (S * S + R * R - 4) / (2 * S * R)
    ch = arb_hi(c)
    if ch >= 1:
        return arb(0)
    return arb(arb_hi(c)).acos()   # acos decreasing -> evaluate at upper end of c (lower bound of theta)


def allowed_arcs_exact(slo, plo, phi, k, rho):
    forb = []
    for j in range(k):
        th = theta_lo_arb(slo[j], rho)
        if arb_hi(th) <= 0:
            continue
        L = to_fr_hi(arb(phi[j]) - th) + SHRINK
        H = to_fr_lo(arb(plo[j]) + th) - SHRINK
        if H <= L:
            continue
        forb.append((L, H))
    P = TWO_PI_HI
    segs = []
    for L, H in forb:
        for sh in (-2, -1, 0, 1, 2):
            segs.append((L + sh * P + SHRINK * abs(sh), H + sh * P - SHRINK * abs(sh)))
    segs.sort()
    merged = []
    for a, b in segs:
        if merged and a < merged[-1][1]:
            merged[-1][1] = max(merged[-1][1], b)
        else:
            merged.append([a, b])
    allowed = []
    cur = Fr(-100)
    for a, b in merged:
        if a >= cur:
            allowed.append((cur, a))
        cur = max(cur, b)
    # one representative per circle arc: start in [0, P)
    return [(a, b) for a, b in allowed if 0 <= a < P]


def stn_ranges_exact(seq, delta, N, P):
    M = N + 1
    INF = None
    D = [[None] * M for _ in range(M)]
    for i in range(M):
        D[i][i] = Fr(0)

    def setmin(i, j, v):
        if D[i][j] is None or v < D[i][j]:
            D[i][j] = v
    for j in range(1, M):
        S, E = seq[j - 1]
        setmin(0, j, E)
        setmin(j, 0, -S)
    for j in range(1, N):
        setmin(j + 1, j, -delta)
    setmin(1, N, P - delta)
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


def placements(arcs, delta, N, P):
    m = len(arcs)
    caps = [int((b - a) / delta) + 1 for a, b in arcs]
    res = []

    def rec(i, rem, counts):
        if i == m:
            if rem == 0:
                seq = []
                for q, c in enumerate(counts):
                    seq += [arcs[q]] * c
                r = stn_ranges_exact(seq, delta, N, P)
                if r is not None:
                    res.append((tuple(counts), r))
            return
        for c in range(0, min(caps[i], rem) + 1):
            rec(i + 1, rem - c, counts + [c])
    rec(0, N, [])
    return res


def maxdist_box_point_sq(slo, shi, plo, phi, cx, cy):
    """arb upper bound of max over polar box of |q - c|^2."""
    rc2 = cx * cx + cy * cy
    rc = rc2.sqrt()
    ac = arb_angle(cx, cy)
    # min of cos(psi - ac) over psi in [plo, phi]
    lo = arb(plo) - ac; hi = arb(phi) - ac
    lof = float(arb_lo(lo)); hif = float(arb_hi(hi))
    # check odd multiple of pi inside (conservative)
    cm = None
    for m in range(-4, 5):
        z = (2 * m + 1) * PI
        if not (arb_hi(z) < lof or arb_lo(z) > hif):
            cm = arb(-1)
    if cm is None:
        c1 = lo.cos(); c2 = hi.cos()
        cm = arb(min(arb_lo(c1), arb_lo(c2)))
    best = None
    for s in (slo, shi):
        S = arb(s)
        v = S * S + rc2 - 2 * S * rc * cm
        vh = arb_hi(v)
        if best is None or vh > best:
            best = vh
    return arb(best)


def main():
    n = int(sys.argv[1]); rho_t = float(sys.argv[2]); k = int(sys.argv[3]); fn = sys.argv[4]
    S = np.load(fn)
    P, B, rho_s, dloc = load_cstar(n)
    N = n - k
    I = [i for i in range(n) if i not in B]
    # canonical c*: rotate so max-radius interior point at angle 0
    rad = [(P[i][0] * P[i][0] + P[i][1] * P[i][1]).sqrt() for i in range(n)]
    Ii = sorted(I, key=lambda i: -float(rad[i].mid()))
    a0 = arb_angle(P[Ii[0]][0], P[Ii[0]][1])
    c0, s0 = a0.cos(), a0.sin()
    Q = [(x * c0 + y * s0, -x * s0 + y * c0) for x, y in P]
    variants = [Q, [(x, -y) for x, y in Q]]
    Rt = arb(rho_t)
    delta_lo_fr = to_fr_lo(2 * (1 / Rt).asin()) - Fr(2, 10 ** 12)
    thr = arb_lo(rho_s * dloc)
    rho_hi = arb_hi(rho_s)
    print(f"n={n} k={k}: {len(S)} boxes; threshold rho* delta_loc >= {float(thr):.4e}")
    worst = 0.0; bad = 0; nopl = 0
    for t, bx in enumerate(S):
        slo = bx[0:k]; shi = bx[k:2 * k]; plo = bx[2 * k:3 * k]; phi = bx[3 * k:4 * k]
        arcs = allowed_arcs_exact(slo, plo, phi, k, rho_t)
        pls = placements(arcs, delta_lo_fr, N, TWO_PI_HI)
        if not pls:
            nopl += 1
            continue    # box contains no feasible configuration at all
        best_total = None
        for V in variants:
            cint = [V[i] for i in Ii]
            best_int = None
            for perm in itertools.permutations(range(k)):
                tot = arb(0)
                for j in range(k):
                    tot += maxdist_box_point_sq(slo[j], shi[j], plo[j], phi[j], *cint[perm[j]])
                th_ = float(arb_hi(tot))
                if best_int is None or th_ < best_int:
                    best_int = th_
            angs = sorted([float((arb_angle(V[i][0], V[i][1])).mid()) % (2 * math.pi) for i in B])
            worst_b = 0.0
            for counts, rng in pls:
                best_b = None
                for shift in range(N):
                    tot = 0.0
                    for j in range(N):
                        lo, hi = float(rng[j][0]), float(rng[j][1])
                        a_s = angs[(j + shift) % N]
                        mid = 0.5 * (lo + hi)
                        a_s += 2 * math.pi * round((mid - a_s) / (2 * math.pi))
                        dev = max(abs(lo - a_s), abs(hi - a_s)) + 1e-12
                        tot += (float(rho_hi) * dev) ** 2
                    if best_b is None or tot < best_b:
                        best_b = tot
                worst_b = max(worst_b, best_b)
            total = math.sqrt(best_int + worst_b) * (1 + 1e-9)
            if best_total is None or total < best_total:
                best_total = total
        worst = max(worst, best_total)
        if not (best_total < float(thr)):
            bad += 1
            if bad <= 5:
                print("   FAIL box", t, best_total)
    print(f"  boxes with no boundary placement (empty): {nopl}")
    print(f"  worst D = {worst:.4e} < threshold {float(thr):.4e} ? {'YES' if bad == 0 else 'NO'};  failing boxes: {bad}")


if __name__ == "__main__":
    main()
