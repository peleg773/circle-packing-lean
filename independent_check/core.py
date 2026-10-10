"""
Independent verifier: core geometric primitives for the 15-circle problem.

Everything here is written from scratch from the problem statement only.

Conventions
-----------
* Unit circles, centres c_i, |c_i - c_j| >= 2, |c_i| <= rho.
* Interior point i is described by a polar box  B[i] = [s_lo, s_hi, p_lo, p_hi]
  (radius interval, angle interval; angles are real numbers, a box never wraps,
  the circle is handled by explicit +-2pi shifts).
* All pruning decisions use float64 with explicit safety margins (EPS_* below),
  which are >= 1e-9 while every floating-point error in the quantities involved is
  <= ~1e-13 (well-conditioned formulas are used everywhere, see REPORT.md).
"""
import math
import numpy as np
from numba import njit

TWO_PI = 2.0 * math.pi
PI = math.pi

# --- safety margins -------------------------------------------------------
EPS_ARC = 1e-9      # every certainly-forbidden boundary arc is shrunk by this on both sides
EPS_DB = 1e-9       # boundary-boundary separation used in the capacity bound is delta_B - EPS_DB
EPS_D2 = 1e-9       # a pair is declared too close only if max|Pi-Pj|^2 < 4 - EPS_D2
EPS_ANG = 1e-9      # interior-interior angular exclusion half-width is reduced by this
EPS_H = 1e-13       # absolute slack on sin^2(half angle) quantities before asin


def constants(rho):
    """Return the derived constants for a given rho (float), computed with
    outward safety: R_I is rounded UP, delta_B is rounded DOWN."""
    from flint import arb, ctx
    old = ctx.prec
    ctx.prec = 200
    r = arb(rho)
    RI = (r * r - 4).sqrt()
    dB = 2 * (1 / r).asin()
    ctx.prec = old
    RI_hi = float(RI.mid()) + 1e-12
    dB_lo = float(dB.mid()) - EPS_DB
    rho_m2 = rho - 2.0          # exact in binary floating point (Sterbenz)
    return RI_hi, dB_lo, rho_m2


@njit(cache=True)
def theta_f(s, rho, rho_m2):
    """Half-width theta(s) of the angular arc a boundary centre must avoid around an
    interior centre at radius s:  cos(theta) = (s^2 + rho^2 - 4)/(2 s rho).
    Stable form: sin^2(theta/2) = (s-(rho-2))(2+rho-s)/(4 rho s).  0 if s <= rho-2."""
    a = s - rho_m2              # exact for s in [rho_m2/2, 2 rho_m2] (Sterbenz)
    if a <= 0.0:
        return 0.0
    x = a * (2.0 + rho - s) / (4.0 * rho * s)
    if x >= 1.0:
        return PI
    return 2.0 * math.asin(math.sqrt(x))


@njit(cache=True)
def cos_min_interval(dlo, dhi):
    """min of cos(t) over t in [dlo, dhi]."""
    if dhi - dlo >= TWO_PI:
        return -1.0
    # does [dlo, dhi] contain pi + 2 pi n ?
    n = math.ceil((dlo - PI) / TWO_PI)
    if PI + TWO_PI * n <= dhi:
        return -1.0
    c1 = math.cos(dlo)
    c2 = math.cos(dhi)
    return c1 if c1 < c2 else c2


@njit(cache=True)
def maxdist2(a_lo, a_hi, pa_lo, pa_hi, b_lo, b_hi, pb_lo, pb_hi):
    """Exact max of |P-Q|^2 over P in polar box a, Q in polar box b."""
    cm = cos_min_interval(pa_lo - pb_hi, pa_hi - pb_lo)
    best = -1.0
    for si in (a_lo, a_hi):
        for sj in (b_lo, b_hi):
            v = si * si + sj * sj - 2.0 * si * sj * cm
            if v > best:
                best = v
    return best


@njit(cache=True)
def min_ang_sep(a_lo, a_hi, b_lo, b_hi):
    """Lower bound D on the circular angle between two centres with radii in
    [a_lo,a_hi], [b_lo,b_hi] that are >= 2 apart.  sin^2(D/2) = min over the 4 radius
    corners of h = (4-(si-sj)^2)/(4 si sj) (the minimum is attained at a corner).
    Returns -1 if the pair is infeasible for every radius choice (h > 1 everywhere),
    0 if there is no angular constraint."""
    hmin = 1e300
    for si in (a_lo, a_hi):
        for sj in (b_lo, b_hi):
            d = si - sj
            num = 4.0 - d * d
            den = 4.0 * si * sj
            if den <= 0.0:
                h = 1e300 if num > 0.0 else -1e300
            else:
                h = num / den
            if h < hmin:
                hmin = h
    if hmin <= EPS_H:
        return 0.0
    if hmin > 1.0 + 1e-9:
        return -1.0
    x = hmin - EPS_H
    if x > 1.0:
        x = 1.0
    D = 2.0 * math.asin(math.sqrt(x)) - EPS_ANG
    if D < 0.0:
        D = 0.0
    return D


@njit(cache=True)
def remove_arc(lo, hi, fa, fb):
    """Remove the open arc (fa, fb) (mod 2pi) from the real interval [lo, hi] when it
    covers an end.  Returns (lo, hi, ok)."""
    for rep in range(2):
        for sh in (-TWO_PI, 0.0, TWO_PI):
            a = fa + sh
            b = fb + sh
            if a < lo and b > lo:
                lo = b
            if a < hi and b > hi:
                hi = a
            if lo > hi:
                return lo, hi, False
    return lo, hi, True


@njit(cache=True)
def capacity_ub(arc_a, arc_b, n, db, need):
    """Upper bound on the number of points on the circle with pairwise circular distance
    >= db avoiding the open arcs (arc_a[i], arc_b[i]), i<n (each of length < 2pi).
    Exact for the given (already conservatively shrunk) arcs: tries every left endpoint of
    an allowed arc as first point and places greedily.  Returns early when >= need."""
    if n == 0:
        c = 0
        x = 0.0
        while x <= TWO_PI - db + 1e-12:
            c += 1
            x += db
        return c
    # normalise starts to [0, 2pi)
    A = np.empty(n)
    L = np.empty(n)
    for i in range(n):
        a = arc_a[i]
        a = a - TWO_PI * math.floor(a / TWO_PI)
        if a >= TWO_PI:
            a -= TWO_PI
        A[i] = a
        L[i] = arc_b[i] - arc_a[i]
        if L[i] >= TWO_PI:
            return 0
    # find an allowed reference point: the end of some arc not strictly inside another arc
    ref = -1.0
    for i in range(n):
        e = A[i] + L[i]
        inside = False
        for j in range(n):
            if j == i:
                continue
            # is e in (A[j], A[j]+L[j]) mod 2pi ?
            t = e - A[j]
            t = t - TWO_PI * math.floor(t / TWO_PI)
            if t > 1e-12 and t < L[j] - 1e-12:
                inside = True
                break
        if not inside:
            ref = e
            break
    if ref < 0.0:
        return 0
    # rotate so that ref -> 0; shrink every arc by an extra 1e-12 (keeps it an upper bound)
    S = np.empty(n)
    E = np.empty(n)
    m = 0
    for i in range(n):
        a = A[i] - ref + 1e-12
        a = a - TWO_PI * math.floor(a / TWO_PI)
        ln = L[i] - 2e-12
        if ln <= 0.0:
            continue
        b = a + ln
        if b > TWO_PI:
            b = TWO_PI
        if a < 0.0:
            a = 0.0
        S[m] = a
        E[m] = b
        m += 1
    if m == 0:
        c = 0
        x = 0.0
        while x <= TWO_PI - db + 1e-12:
            c += 1
            x += db
        return c
    order = np.argsort(S[:m])
    # merge
    MS = np.empty(m)
    ME = np.empty(m)
    nm = 0
    for t in range(m):
        i = order[t]
        if nm > 0 and S[i] < ME[nm - 1]:
            if E[i] > ME[nm - 1]:
                ME[nm - 1] = E[i]
        else:
            MS[nm] = S[i]
            ME[nm] = E[i]
            nm += 1
    # allowed closed arcs: [0, MS[0]], [ME[0], MS[1]], ..., [ME[nm-2], MS[nm-1]], [ME[nm-1], 2pi]
    na = nm + 1
    AL = np.empty(na)
    AU = np.empty(na)
    AL[0] = 0.0
    AU[0] = MS[0]
    for t in range(1, nm):
        AL[t] = ME[t - 1]
        AU[t] = MS[t]
    AL[nm] = ME[nm - 1]
    AU[nm] = TWO_PI
    best = 0
    for j in range(na):
        start = AL[j]
        limit = start + TWO_PI - db
        cnt = 1
        x = start
        idx = j
        wrap = 0.0
        while True:
            x = x + db
            # advance to the allowed arc containing x or the next one
            while True:
                if idx >= na:
                    idx = 0
                    wrap += TWO_PI
                u = AU[idx] + wrap
                if u >= x:
                    break
                idx += 1
            l = AL[idx] + wrap
            if l > x:
                x = l
            if x > limit + 1e-12:
                break
            cnt += 1
            if cnt > 40:
                break
        if cnt > best:
            best = cnt
            if best >= need:
                return best
    return best


@njit(cache=True)
def capacity_ws(arc_a, arc_b, n, db, need, W):
    """Same as capacity_ub but allocation-free.  W: float workspace of shape (8, >= n+2)."""
    if n == 0:
        c = 0
        x = 0.0
        while x <= TWO_PI - db + 1e-12:
            c += 1
            x += db
        return c
    A = W[0]
    L = W[1]
    for i in range(n):
        a = arc_a[i]
        a = a - TWO_PI * math.floor(a / TWO_PI)
        if a >= TWO_PI:
            a -= TWO_PI
        A[i] = a
        L[i] = arc_b[i] - arc_a[i]
        if L[i] >= TWO_PI:
            return 0
    ref = -1.0
    for i in range(n):
        e = A[i] + L[i]
        inside = False
        for j in range(n):
            if j == i:
                continue
            t = e - A[j]
            t = t - TWO_PI * math.floor(t / TWO_PI)
            if t > 1e-12 and t < L[j] - 1e-12:
                inside = True
                break
        if not inside:
            ref = e
            break
    if ref < 0.0:
        return 0
    S = W[2]
    E = W[3]
    m = 0
    for i in range(n):
        a = A[i] - ref + 1e-12
        a = a - TWO_PI * math.floor(a / TWO_PI)
        ln = L[i] - 2e-12
        if ln <= 0.0:
            continue
        b = a + ln
        if b > TWO_PI:
            b = TWO_PI
        if a < 0.0:
            a = 0.0
        # insertion sort by start
        p = m
        while p > 0 and S[p - 1] > a:
            S[p] = S[p - 1]
            E[p] = E[p - 1]
            p -= 1
        S[p] = a
        E[p] = b
        m += 1
    if m == 0:
        c = 0
        x = 0.0
        while x <= TWO_PI - db + 1e-12:
            c += 1
            x += db
        return c
    MS = W[4]
    ME = W[5]
    nm = 0
    for t in range(m):
        if nm > 0 and S[t] < ME[nm - 1]:
            if E[t] > ME[nm - 1]:
                ME[nm - 1] = E[t]
        else:
            MS[nm] = S[t]
            ME[nm] = E[t]
            nm += 1
    na = nm + 1
    AL = W[6]
    AU = W[7]
    AL[0] = 0.0
    AU[0] = MS[0]
    for t in range(1, nm):
        AL[t] = ME[t - 1]
        AU[t] = MS[t]
    AL[nm] = ME[nm - 1]
    AU[nm] = TWO_PI
    best = 0
    for j in range(na):
        start = AL[j]
        limit = start + TWO_PI - db
        cnt = 1
        x = start
        idx = j
        wrap = 0.0
        while True:
            x = x + db
            while True:
                if idx >= na:
                    idx = 0
                    wrap += TWO_PI
                u = AU[idx] + wrap
                if u >= x:
                    break
                idx += 1
            l = AL[idx] + wrap
            if l > x:
                x = l
            if x > limit + 1e-12:
                break
            cnt += 1
            if cnt > 40:
                break
        if cnt > best:
            best = cnt
            if best >= need:
                return best
    return best


@njit(cache=True)
def radial_forbidden(s_lo_j, s_hi_j, cm):
    """For a centre P_i at radius s (unknown) and P_j in a box with radius in
    [s_lo_j, s_hi_j] and cos(angle difference) >= cm over the box, return an open
    interval (u, v) of radii s for which max|P_i - P_j| < 2 over the box, shrunk by 1e-9
    on both sides (u >= v means empty)."""
    u = -1e300
    v = 1e300
    for sj in (s_lo_j, s_hi_j):
        disc = 4.0 - sj * sj * (1.0 - cm * cm)
        if disc <= 0.0:
            return 0.0, -1.0
        r = math.sqrt(disc)
        r1 = sj * cm - r
        r2 = sj * cm + r
        if r1 > u:
            u = r1
        if r2 < v:
            v = r2
    return u + 1e-9, v - 1e-9


def excess_lemma_margin(rho, prec=128):
    """Rigorous (arb) check of the hypothesis of the excess lemma (rule R5):
        D(s_i, s_j) >= theta(s_i) + theta(s_j) - delta_B   for all s_i, s_j in [s_e, R_I],
    where s_e = the radius with 2 theta(s_e) = delta_B (points with smaller radius have
    zero excess), D = min angular separation of two interior centres >= 2 apart.
    Sufficient: min over the 4 corners of [s_e_lo, R_I]^2 of D  >=  2 theta(R_I) - delta_B
    (D is minimised at a corner, theta is increasing).  Returns a float lower bound of
    (min corner D) - (2 theta(R_I) - delta_B); the lemma holds if it is > 0."""
    from flint import arb, ctx
    old = ctx.prec
    ctx.prec = prec
    r = arb(rho)
    RI = (r * r - 4).sqrt()
    dB = 2 * (1 / r).asin()

    def th(s):
        x = (s - (r - 2)) * (2 + r - s) / (4 * r * s)
        return 2 * x.sqrt().asin()
    # s_e: lower bound by bisection on floats (theta increasing): largest float s with
    # 2 theta(s) < delta_B certainly
    lo, hi = float((r - 2).mid()) + 1e-9, float(RI.mid())
    for _ in range(80):
        mid = 0.5 * (lo + hi)
        if 2 * th(arb(mid)) < dB:
            lo = mid
        else:
            hi = mid
    s_e = arb(lo)   # 2 theta(s) < delta_B for s <= lo, so points with e>0 have s > lo

    def D(a, b):
        h = (4 - (a - b) ** 2) / (4 * a * b)
        return 2 * h.sqrt().asin()
    corners = [D(s_e, s_e), D(s_e, RI), 2 * (1 / RI).asin()]   # D(RI,RI) = 2 asin(1/RI)
    dmin_lo = min(float(cn.lower()) for cn in corners)
    need = 2 * th(RI) - dB
    marg = dmin_lo - float(need.upper())
    ctx.prec = old
    # (float rounding of the two bounds: |error| < 1e-16, irrelevant against the margin)
    return marg - 1e-15, lo


def excess_slack(rho, m, db_lo):
    """Slack used by rule R5: 2pi - m*delta_B (upper bound) if the excess lemma is proven
    for this rho, otherwise +inf (rule R5 disabled)."""
    if m < 1:
        return 1e300          # the lemma needs at least one boundary centre (gaps exist)
    marg, _ = excess_lemma_margin(rho)
    if marg > 0.0:
        return 2.0 * math.pi - m * db_lo
    return 1e300
