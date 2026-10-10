"""ringbb: branch-and-bound over INTERIOR configurations for n equal circles in a circle.

Normalisation: unit circles <-> centres with pairwise distance >= 2, centres within radius rho.

Reduction (see docs/lemmas.md, L1-L3):
  * Push-out lemma: WLOG every centre is either on the circle |c| = rho ("boundary point")
    or satisfies |c| <= R_I := sqrt(rho^2 - 4) ("interior point").
  * Given the interior points I, a boundary point at angle a is admissible iff for every q=(s,psi) in I
    with s > rho-2:  |a - psi|_circ >= theta(s) := arccos((s^2+rho^2-4)/(2 s rho)).
    Boundary points need pairwise angular separation >= delta_B := 2 arcsin(1/rho).
    => configuration with k interior points exists  iff  Bmax(I) >= n-k  (Bmax exact via greedy).
  * Reduction lemma: WLOG k is minimal; then Bmax(I) <= n-k (else move a point to the boundary).

Search (for each k): interior points ordered by radius s_1 >= s_2 >= ... >= s_k, psi_1 = 0 (rotation),
psi_2 in [0, pi] (reflection).  Boxes in polar coordinates.  A box is discarded if
  (P1) some pair has max distance < 2 (exact max over the polar boxes, convexity),
  (P2) Bmax computed with CERTAINLY-forbidden arcs (shrunk) and delta_B - eps is < n-k,
  (P3) Bmax computed with POSSIBLY-forbidden arcs (enlarged) and delta_B + eps is >= n-k+1,
  (P4) ordering / packing-radius bounds violated:  s_j >= rhoM[k-j+1] (known optimal radii).
Floating point with explicit safety margins (EPS) -- final certificate to be re-verified with arb.
"""
import math, sys, time, json, os
import numpy as np
import numba as nb

TWO_PI = 2.0 * math.pi
EPS = 1e-9   # safety margin (radians / squared-distance units); >> rounding error

# optimal container radii for centres (unit circles), m = 0..13  (rho_m = R_m - 1)
# proven values: m<=13 (Pirl 1969 m<=10, Melissen 1994 m=11, Fodor 2000/2003 m=12,13)
# values rounded DOWN to be safe lower bounds
RHO_M = np.array([
    0.0,                 # m=0 (unused)
    0.0,                 # m=1
    1.0,                 # m=2
    1.1547005383792515,  # m=3 2/sqrt3
    1.4142135623730950,  # m=4 sqrt2
    1.7013016167040798,  # m=5 1/sin36
    2.0,                 # m=6
    2.0,                 # m=7
    2.3047648709624865,  # m=8 1/sin(pi/7)
    2.6131259297527530,  # m=9 1/sin(pi/8)
    2.8130250,           # m=10 (R_10 = 3.813026...)  truncated
    2.9238044001630872,  # m=11 1/sin(pi/9)
    3.0296,              # m=12 (R_12 = 4.029609...) truncated
    3.2360679774997896,  # m=13 1+sqrt5
]) - 1e-12


@nb.njit(cache=True)
def theta_of(s, rho):
    """half-width of the arc of the circle |c|=rho forbidden by an interior point at radius s (0 if none)."""
    if s <= rho - 2.0:
        return 0.0
    c = (s * s + rho * rho - 4.0) / (2.0 * s * rho)
    if c >= 1.0:
        return 0.0
    if c <= -1.0:
        return math.pi
    return math.acos(c)


@nb.njit(cache=True)
def bmax_arcs(a_lo, a_hi, m, delta):
    """max # points on the circle with pairwise circular distance >= delta avoiding the OPEN arcs
    (a_lo[i], a_hi[i]) (a_lo < a_hi, a_hi - a_lo < 2pi, a_lo in [0,2pi)).  Exact for exact data."""
    full = int(math.floor(TWO_PI / delta + 1e-12))
    if m == 0:
        return full
    L = np.empty(2 * m); H = np.empty(2 * m)
    c = 0
    for i in range(m):
        lo = a_lo[i]; hi = a_hi[i]
        if hi - lo >= TWO_PI:
            return 0
        if hi > TWO_PI:
            L[c] = lo; H[c] = TWO_PI + 1.0; c += 1      # covers (lo, 2pi]
            L[c] = -1.0; H[c] = hi - TWO_PI; c += 1      # covers [0, hi-2pi)
        else:
            L[c] = lo; H[c] = hi; c += 1
    idx = np.argsort(L[:c])
    Ls = L[:c][idx]; Hs = H[:c][idx]
    ML = np.empty(c); MH = np.empty(c); mm = 0
    for i in range(c):
        if mm > 0 and Ls[i] < MH[mm - 1]:
            if Hs[i] > MH[mm - 1]:
                MH[mm - 1] = Hs[i]
        else:
            ML[mm] = Ls[i]; MH[mm] = Hs[i]; mm += 1
    AS = np.empty(mm + 1); AE = np.empty(mm + 1); na = 0
    cur = 0.0
    for i in range(mm):
        if ML[i] >= cur:
            AS[na] = cur; AE[na] = ML[i]; na += 1
        if MH[i] > cur:
            cur = MH[i]
    if cur <= TWO_PI:
        AS[na] = cur; AE[na] = TWO_PI; na += 1
    if na == 0:
        return 0
    if na == 1 and AS[0] == 0.0 and AE[0] == TWO_PI:
        return full
    if na >= 2 and AS[0] == 0.0 and AE[na - 1] == TWO_PI:
        AS[0] = AS[na - 1]; AE[0] = TWO_PI + AE[0]
        na -= 1
    order = np.argsort(AS[:na])
    S = AS[:na][order]; E = AE[:na][order]
    best = 0
    for st in range(na):
        x0 = S[st]
        count = 1
        x = x0
        limit = x0 + TWO_PI - delta
        while True:
            nxt = x + delta
            if nxt > limit:
                break
            pos = 1e300
            for lift in range(3):
                off = lift * TWO_PI
                for q in range(na):
                    s0 = S[q] + off; e0 = E[q] + off
                    if e0 < nxt:
                        continue
                    cand = nxt if s0 <= nxt else s0
                    if cand < pos:
                        pos = cand
                if pos < 1e299:
                    break
            if pos > limit:
                break
            x = pos
            count += 1
        if count > best:
            best = count
    return best


@nb.njit(cache=True)
def wrap0(x):
    y = x % TWO_PI
    if y < 0:
        y += TWO_PI
    return y


@nb.njit(cache=True)
def bmax_box(slo, shi, plo, phi, k, rho, delta, certain):
    """certain=True: Bmax upper bound (certainly-forbidden arcs, shrunk; delta-EPS).
       certain=False: Bmax lower bound (possibly-forbidden arcs, enlarged; delta+EPS)."""
    a_lo = np.empty(k); a_hi = np.empty(k); m = 0
    for j in range(k):
        if certain:
            w = theta_of(slo[j], rho)
            if w <= 0.0:
                continue
            lo = phi[j] - w + EPS
            hi = plo[j] + w - EPS
            if hi <= lo:
                continue
        else:
            w = theta_of(shi[j], rho)
            if w <= 0.0:
                continue
            lo = plo[j] - w - EPS
            hi = phi[j] + w + EPS
            if hi - lo >= TWO_PI:
                return 0
        base = wrap0(lo)
        a_lo[m] = base; a_hi[m] = base + (hi - lo); m += 1
    if certain:
        return bmax_arcs(a_lo, a_hi, m, delta - EPS)
    else:
        return bmax_arcs(a_lo, a_hi, m, delta + EPS)


@nb.njit(cache=True)
def cos_min_over(dlo, dhi):
    """min of cos over [dlo, dhi] (dhi - dlo <= 2pi)."""
    if dhi - dlo >= TWO_PI:
        return -1.0
    # does the interval contain pi + 2 pi m ?
    m = math.ceil((dlo - math.pi) / TWO_PI)
    if math.pi + m * TWO_PI <= dhi:
        return -1.0
    return min(math.cos(dlo), math.cos(dhi))


@nb.njit(cache=True)
def maxdist2(sa_lo, sa_hi, pa_lo, pa_hi, sb_lo, sb_hi, pb_lo, pb_hi):
    c = cos_min_over(pa_lo - pb_hi, pa_hi - pb_lo)
    best = -1.0
    for sa in (sa_lo, sa_hi):
        for sb in (sb_lo, sb_hi):
            v = sa * sa + sb * sb - 2.0 * sa * sb * c
            if v > best:
                best = v
    return best


@nb.njit(cache=True)
def box_ok(slo, shi, plo, phi, k, n, rho, delta, RI, rhoM, use_reduction):
    """returns 0 if box survives, else a code >0 giving the prune reason."""
    # P4 ordering & radius bounds
    for j in range(k):
        if shi[j] > RI:
            shi[j] = RI
        lb = rhoM[k - j]   # points j..k-1 (k-j of them) inside radius s_j
        if slo[j] < lb:
            slo[j] = lb
        if j > 0 and shi[j] > shi[j - 1]:
            shi[j] = shi[j - 1]
        if slo[j] > shi[j]:
            return 4
    # ordering lower bound propagation backwards: s_{j-1} >= s_j
    for j in range(k - 1, 0, -1):
        if slo[j - 1] < slo[j]:
            slo[j - 1] = slo[j]
        if slo[j - 1] > shi[j - 1]:
            return 4
    # P1 pairwise
    for a in range(k):
        for b in range(a + 1, k):
            if maxdist2(slo[a], shi[a], plo[a], phi[a], slo[b], shi[b], plo[b], phi[b]) < 4.0 - EPS:
                return 1
    # P2a measure bound (radius only; valid since shrunk arcs of gap points are pairwise disjoint, lemma L4)
    budget = TWO_PI - (n - k) * (delta - EPS)
    tot = 0.0
    for j in range(k):
        e = 2.0 * theta_of(slo[j], rho) - delta
        if e > 0.0:
            tot += e
    if tot > budget + EPS:
        return 5
    # P2 boundary upper bound
    if bmax_box(slo, shi, plo, phi, k, rho, delta, True) < n - k:
        return 2
    # P3 reduction
    if use_reduction:
        if bmax_box(slo, shi, plo, phi, k, rho, delta, False) >= n - k + 1:
            return 3
    return 0


@nb.njit(cache=True)
def choose_split(slo, shi, plo, phi, k):
    best = -1.0; bj = -1; bc = 0
    for j in range(k):
        ws = shi[j] - slo[j]
        wp = (phi[j] - plo[j]) * shi[j]
        if ws > best:
            best = ws; bj = j; bc = 0
        if wp > best:
            best = wp; bj = j; bc = 1
    return bj, bc, best


@nb.njit(cache=True)
def run_bb_box(n, k, rho, rhoM, tol, use_reduction, max_boxes, b0):
    delta = 2.0 * math.asin(1.0 / rho)
    RI = math.sqrt(rho * rho - 4.0)
    # stack of boxes: arrays of shape (cap, 4k)
    cap = 1 << 16
    stack = np.empty((cap, 4 * k))
    sp = 0
    stack[0] = b0; sp = 1
    nproc = 0
    reasons = np.zeros(6, np.int64)
    surv = np.empty((200000, 4 * k)); ns = 0
    maxw_surv = 0.0
    while sp > 0:
        sp -= 1
        bx = stack[sp].copy()
        nproc += 1
        if nproc > max_boxes:
            break
        slo = bx[0:k]; shi = bx[k:2 * k]; plo = bx[2 * k:3 * k]; phi = bx[3 * k:4 * k]
        r = box_ok(slo, shi, plo, phi, k, n, rho, delta, RI, rhoM, use_reduction)
        if r > 0:
            reasons[r] += 1
            continue
        j, c, w = choose_split(slo, shi, plo, phi, k)
        if w < tol:
            if ns < surv.shape[0]:
                surv[ns] = bx; ns += 1
            continue
        if sp + 2 >= cap:
            # out of stack: record as survivor (unresolved)
            if ns < surv.shape[0]:
                surv[ns] = bx; ns += 1
            continue
        b1 = bx.copy(); b2 = bx.copy()
        if c == 0:
            mid = 0.5 * (slo[j] + shi[j])
            b1[k + j] = mid; b2[j] = mid
        else:
            mid = 0.5 * (plo[j] + phi[j])
            b1[3 * k + j] = mid; b2[2 * k + j] = mid
        stack[sp] = b1; sp += 1
        stack[sp] = b2; sp += 1
    return nproc, reasons, surv[:ns], sp


def initial_box(k, rho):
    RI = math.sqrt(rho * rho - 4.0)
    b0 = np.empty(4 * k)
    for j in range(k):
        b0[j] = 0.0; b0[k + j] = RI; b0[2 * k + j] = 0.0; b0[3 * k + j] = TWO_PI
    b0[2 * k] = 0.0; b0[3 * k] = 0.0
    if k >= 2:
        b0[3 * k + 1] = math.pi
    return b0


def split_box(bx, k):
    slo = bx[0:k]; shi = bx[k:2 * k]; plo = bx[2 * k:3 * k]; phi = bx[3 * k:4 * k]
    j, c, w = choose_split(slo, shi, plo, phi, k)
    b1 = bx.copy(); b2 = bx.copy()
    if c == 0:
        mid = 0.5 * (slo[j] + shi[j]); b1[k + j] = mid; b2[j] = mid
    else:
        mid = 0.5 * (plo[j] + phi[j]); b1[3 * k + j] = mid; b2[2 * k + j] = mid
    return b1, b2


def presplit(n, k, rho, target):
    delta = 2 * math.asin(1 / rho); RI = math.sqrt(rho * rho - 4)
    boxes = [initial_box(k, rho)]
    while len(boxes) < target:
        new = []
        for bx in boxes:
            b = bx.copy()
            r = box_ok(b[0:k], b[k:2*k], b[2*k:3*k], b[3*k:4*k], k, n, rho, delta, RI, RHO_M, True)
            if r > 0:
                continue
            b1, b2 = split_box(b, k)
            new += [b1, b2]
        if not new:
            break
        boxes = new
    return boxes


def _worker(args):
    n, k, rho, tol, maxb, bx = args
    nproc, reasons, surv, sp = run_bb_box(n, k, rho, RHO_M, tol, True, maxb, bx)
    return nproc, reasons, surv, sp


def solve_k(n, k, rho, tol, maxb_per_box=int(1e9), nworkers=19, target=4000):
    from multiprocessing import Pool
    boxes = presplit(n, k, rho, target)
    t0 = time.time()
    with Pool(nworkers) as pool:
        res = pool.map(_worker, [(n, k, rho, tol, maxb_per_box, b) for b in boxes], chunksize=1)
    nproc = sum(r[0] for r in res)
    reasons = sum(r[1] for r in res)
    surv = np.concatenate([r[2] for r in res]) if any(len(r[2]) for r in res) else np.empty((0, 4 * k))
    unfinished = sum(1 for r in res if r[3] > 0 or r[0] > maxb_per_box)
    return nproc, reasons, surv, unfinished, time.time() - t0, len(boxes)


def main():
    n = int(sys.argv[1]); rho = float(sys.argv[2]); kmin = int(sys.argv[3]); kmax = int(sys.argv[4])
    tol = float(sys.argv[5]) if len(sys.argv) > 5 else 1e-3
    maxb = int(float(sys.argv[6])) if len(sys.argv) > 6 else int(1e9)
    delta = 2 * math.asin(1 / rho); RI = math.sqrt(rho * rho - 4)
    print(f"n={n} rho={rho!r} delta_B={math.degrees(delta):.6f} deg  2pi/delta={2*math.pi/delta:.4f}  R_I={RI:.6f}  rho-2={rho-2:.6f}", flush=True)
    for k in range(kmin, kmax + 1):
        nproc, reasons, surv, unf, dt, nb0 = solve_k(n, k, rho, tol, maxb)
        print(f"  k={k:2d}: presplit={nb0} boxes={nproc:,}  pruned[pair,bnd,red,order,measure]={reasons[1]},{reasons[2]},{reasons[3]},{reasons[4]},{reasons[5]}  survivors={len(surv)}  unfinished_subtrees={unf}  time={dt:.1f}s", flush=True)
        if len(surv):
            S = surv
            print(f"      survivor s-ranges: " + ", ".join(f"[{S[:, j].min():.4f},{S[:, k + j].max():.4f}]" for j in range(k)), flush=True)
            np.save(os.path.join(HERE_OUT, f"surv_n{n}_k{k}.npy"), S)


HERE_OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "out")

if __name__ == "__main__":
    main()
