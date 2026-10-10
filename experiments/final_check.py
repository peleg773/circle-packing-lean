"""Final stage: every surviving k-interior box must lie in the local-uniqueness neighbourhood of c*.

For each survivor box (polar boxes for the k interior points, canonical form: s decreasing, psi_0 = 0,
psi_1 in [0, pi]):
  1. certainly-forbidden arcs at rho_test -> allowed closed arcs on the boundary circle;
  2. enumerate all assignments of the B = n-k boundary points to allowed arcs; for each assignment solve the
     simple temporal network (Floyd-Warshall) -> feasible? and exact range [lo_j, hi_j] of each boundary angle;
  3. bound   D^2 = sum_interior max_{box} |q_j - c*_j|^2 + sum_boundary max |rho* e^{i a_j} - c*_b(j)|^2
     (best matching), and require  D < rho* * delta_loc  (delta_loc from local_certificate_n{n}.json).
All in float64 with safety margins (re-verification in arb: verify_final_arb.py).
Usage: python final_check.py n rho_test k survivors.npy
"""
import sys, os, json, math, itertools
import numpy as np
from ringbb2 import theta_of, EPS, TWO_PI, cos_min_over

HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(HERE)


def load_cstar(n):
    with open(os.path.join(ROOT, "known_packings", f"local_certificate_n{n}.json")) as f:
        C = json.load(f)
    d = float(C["d_star"]); rho = 2.0 / d
    P = np.array([[float(a), float(b)] for a, b in C["points_mid"]]) * rho
    B = C["boundary"]
    I = [i for i in range(n) if i not in B]
    dl = C["delta_loc"].strip("[]").split("+/-")
    dloc = float(dl[0]) - float(dl[1])
    return P, B, I, rho, dloc


def canonical_cstar(P, I, B):
    """rotate/reflect c* so that interior max-radius point is at angle 0 and next one has angle in [0,pi]."""
    r = np.hypot(P[:, 0], P[:, 1])
    Ii = sorted(I, key=lambda i: -r[i])
    out = []
    a0 = math.atan2(P[Ii[0], 1], P[Ii[0], 0])
    c, s = math.cos(-a0), math.sin(-a0)
    Q = P @ np.array([[c, s], [-s, c]])
    # second interior point angle
    a1 = math.atan2(Q[Ii[1], 1], Q[Ii[1], 0]) % TWO_PI
    variants = [Q]
    if abs(a1) < 1e-9 or abs(a1 - math.pi) < 1e-9:
        variants.append(Q * np.array([1, -1]))
    elif a1 > math.pi:
        variants = [Q * np.array([1, -1])]
    # also include reflection if c* is mirror symmetric (harmless to include both)
    variants.append(Q * np.array([1, -1]))
    return variants, Ii


def allowed_arcs(slo, shi, plo, phi, k, rho):
    """allowed closed arcs (S,E), S in [0,2pi), E>=S (lifted), complement of certainly-forbidden open arcs."""
    forb = []
    for j in range(k):
        w = theta_of(slo[j], rho)
        if w <= 0:
            continue
        L = phi[j] - w + EPS; H = plo[j] + w - EPS
        if H <= L:
            continue
        base = L % TWO_PI
        forb.append((base, base + (H - L)))
    if not forb:
        return [(0.0, TWO_PI)]   # whole circle (caller must treat as special)
    segs = []
    for lo, hi in forb:
        for sh in (-TWO_PI, 0.0, TWO_PI):
            segs.append((lo + sh, hi + sh))
    segs.sort()
    merged = []
    for a, b in segs:
        if merged and a < merged[-1][1]:
            merged[-1][1] = max(merged[-1][1], b)
        else:
            merged.append([a, b])
    allowed = []
    cur = -10.0
    for a, b in merged:
        if a >= cur:
            allowed.append((cur, a))
        cur = max(cur, b)
    return [(a, b) for a, b in allowed if 0.0 <= a < TWO_PI]


def stn_ranges(arcs_seq, delta, N):
    """arcs_seq: list of N (S,E) lifted closed intervals in cyclic order (non-decreasing starts, lifted).
    Variables x_1..x_N, x_0 = 0 reference.  Returns None if infeasible else list of (lo,hi)."""
    M = N + 1
    INF = 1e18
    D = np.full((M, M), INF)
    for i in range(M):
        D[i, i] = 0.0
    for j in range(1, M):
        S, E = arcs_seq[j - 1]
        D[0, j] = min(D[0, j], E)       # x_j - x_0 <= E
        D[j, 0] = min(D[j, 0], -S)      # x_0 - x_j <= -S
    for j in range(1, N):
        D[j + 1, j] = min(D[j + 1, j], -delta)   # x_j - x_{j+1} <= -delta
    D[1, N] = min(D[1, N], TWO_PI - delta)        # x_N - x_1 <= 2pi - delta
    for kk in range(M):
        D = np.minimum(D, D[:, kk:kk + 1] + D[kk:kk + 1, :])
    if np.any(np.diag(D) < -1e-12):
        return None
    return [(-D[j, 0], D[0, j]) for j in range(1, M)]


def boundary_placements(arcs, delta, N):
    """enumerate assignments (counts per arc, cyclic order starting from arc 0 lifted) -> list of range-lists."""
    m = len(arcs)
    caps = [int(math.floor((b - a) / delta + 1e-12)) + 1 for a, b in arcs]
    results = []

    def rec(i, remaining, counts):
        if i == m:
            if remaining == 0:
                seq = []
                for q, c in enumerate(counts):
                    seq += [arcs[q]] * c
                rng = stn_ranges(seq, delta, N)
                if rng is not None:
                    results.append((tuple(counts), rng))
            return
        for c in range(0, min(caps[i], remaining) + 1):
            rec(i + 1, remaining - c, counts + [c])

    rec(0, N, [])
    return results


def max_dist_polar_box_to_point(slo, shi, plo, phi, c):
    rc = math.hypot(c[0], c[1]); ac = math.atan2(c[1], c[0])
    cm = cos_min_over(plo - ac, phi - ac)
    best = 0.0
    for s in (slo, shi):
        v = s * s + rc * rc - 2 * s * rc * cm
        best = max(best, v)
    return math.sqrt(max(best, 0.0))


def check_box(bx, k, n, rho_t, variants, Ii, Bidx, rho_s, delta_t):
    slo = bx[0:k]; shi = bx[k:2 * k]; plo = bx[2 * k:3 * k]; phi = bx[3 * k:4 * k]
    N = n - k
    arcs = allowed_arcs(slo, shi, plo, phi, k, rho_t)
    pls = boundary_placements(arcs, delta_t - EPS, N)
    if not pls:
        return 0.0, "no boundary placement (box infeasible)"
    best_total = None
    for Q in variants:
        # interior: try all permutations among equal-radius groups (k<=6 -> brute force all perms is fine)
        cint = Q[Ii]
        best_int = None
        for perm in itertools.permutations(range(k)):
            tot = 0.0
            for j in range(k):
                tot += max_dist_polar_box_to_point(slo[j], shi[j], plo[j], phi[j], cint[perm[j]]) ** 2
                if best_int is not None and tot >= best_int:
                    break
            if best_int is None or tot < best_int:
                best_int = tot
        # boundary: for each placement, best cyclic matching with c* boundary angles
        ab = np.sort(np.arctan2(Q[Bidx, 1], Q[Bidx, 0]) % TWO_PI)
        worst_b = 0.0
        for counts, rng in pls:
            best_b = None
            for shift in range(N):
                tot = 0.0
                for j in range(N):
                    lo, hi = rng[j]
                    a_star = ab[(j + shift) % N]
                    # lift a_star near [lo,hi]
                    mid = 0.5 * (lo + hi)
                    a_star += TWO_PI * round((mid - a_star) / TWO_PI)
                    dev = max(abs(lo - a_star), abs(hi - a_star))
                    tot += (2 * rho_s * math.sin(min(dev, math.pi) / 2)) ** 2
                if best_b is None or tot < best_b:
                    best_b = tot
            worst_b = max(worst_b, best_b)
        total = math.sqrt(best_int + worst_b)
        if best_total is None or total < best_total:
            best_total = total
    return best_total, f"placements={len(pls)}"


def main():
    n = int(sys.argv[1]); rho_t = float(sys.argv[2]); k = int(sys.argv[3]); fn = sys.argv[4]
    S = np.load(fn)
    P, B, I, rho_s, dloc = load_cstar(n)
    variants, Ii = canonical_cstar(P, I, B)
    delta_t = 2 * math.asin(1 / rho_t)
    thr = rho_s * dloc
    print(f"n={n} k={k}: {len(S)} survivor boxes; rho*={rho_s:.15f}; threshold rho*delta_loc={thr:.3e}")
    worst = 0.0; bad = 0
    maxw = 0.0
    for t, bx in enumerate(S):
        D, info = check_box(bx, k, n, rho_t, variants, Ii, B, rho_s, delta_t)
        worst = max(worst, D)
        if D >= thr:
            bad += 1
            if bad <= 5:
                print("  box", t, "D=", D, info)
    print(f"  worst D = {worst:.3e}  (threshold {thr:.3e});  boxes failing: {bad}")


if __name__ == "__main__":
    main()
