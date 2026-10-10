"""
Independent re-implementation of the node test of bnb2.check_node2 in rigorous ball
arithmetic (python-flint arb), WITHOUT the float safety margins.

Every quantity that the float code compares against a threshold is enclosed in an arb
ball and the conservative end of the ball is used.  New box endpoints produced by a
contraction are rounded outward to floats.  The boundary-capacity greedy is run in exact
rational arithmetic (fractions.Fraction) on outward-rounded arc endpoints, with a
rigorous rational upper bound for 2*pi.

Use: replay a random sample of nodes from a B&B run and check that whenever the float
code prunes a node, the rigorous code prunes it too (soundness spot check of the
floating-point layer).
"""
import math
from fractions import Fraction
import numpy as np
from flint import arb, ctx

ctx.prec = 96
PI = arb.pi()
TWOPI = 2 * PI


def fdown(x):
    """float <= every point of the arb ball x"""
    lo = x.lower()
    f = float(lo)
    while arb(f) > lo:          # arb comparison: True only if certainly greater
        f = np.nextafter(f, -np.inf)
    if not (arb(f) <= lo):
        f = np.nextafter(f, -np.inf)
    return float(f)


def fup(x):
    hi = x.upper()
    f = float(hi)
    while arb(f) < hi:
        f = np.nextafter(f, np.inf)
    if not (arb(f) >= hi):
        f = np.nextafter(f, np.inf)
    return float(f)


class Ctx:
    def __init__(self, rho):
        self.rho = arb(rho)
        self.rho_m2 = self.rho - 2
        self.dB = 2 * (1 / self.rho).asin()
        self.RI = (self.rho * self.rho - 4).sqrt()


def theta_lo(c, s):
    """a float lower bound for theta(s) (0 if s <= rho-2 possible)"""
    s = arb(s)
    a = s - c.rho_m2
    if not (a > 0):
        return 0.0
    x = a * (2 + c.rho - s) / (4 * c.rho * s)
    th = 2 * x.sqrt().asin()
    return max(0.0, fdown(th))


def theta_ball(c, s):
    s = arb(s)
    a = s - c.rho_m2
    if not (a > 0):
        return None
    x = a * (2 + c.rho - s) / (4 * c.rho * s)
    return 2 * x.sqrt().asin()


def cos_min_ub(dlo, dhi):
    """an arb ball whose upper end is >= ... we need a LOWER bound of min cos -> returns
    float lower bound of min_{t in [dlo,dhi]} cos t"""
    if dhi - dlo >= 6.3:
        return -1.0
    n = math.ceil((dlo - math.pi) / (2 * math.pi)) - 1
    for nn in (n, n + 1, n + 2):
        t = PI + TWOPI * nn
        # if pi + 2 pi nn could lie in [dlo, dhi] -> min cos = -1
        if not (t < arb(dlo)) and not (t > arb(dhi)):
            return -1.0
    c1 = arb(dlo).cos()
    c2 = arb(dhi).cos()
    return min(fdown(c1), fdown(c2))


def maxdist2_ub(Bi, Bj):
    cm = arb(cos_min_ub(Bi[2] - Bj[3], Bi[3] - Bj[2]))
    # note: Bi[2]-Bj[3] computed in float above: enclose exactly instead
    best = None
    for si in (Bi[0], Bi[1]):
        for sj in (Bj[0], Bj[1]):
            v = arb(si) ** 2 + arb(sj) ** 2 - 2 * arb(si) * arb(sj) * cm
            u = fup(v)
            best = u if best is None else max(best, u)
    return best


def min_ang_sep_lb(a0, a1, b0, b1):
    """float lower bound for the required angular separation; -1 if infeasible."""
    hmin = None
    for si in (a0, a1):
        for sj in (b0, b1):
            d = arb(si) - arb(sj)
            num = 4 - d * d
            den = 4 * arb(si) * arb(sj)
            if not (den > 0):
                h = math.inf if num > 0 else -math.inf
                if not (num > 0) and not (num < 0):
                    h = -math.inf
            else:
                h = fdown(num / den)
            hmin = h if hmin is None else min(hmin, h)
    if hmin <= 0:
        return 0.0
    # infeasible if h > 1 for all corners -> s_i + s_j < 2 for all corners
    if hmin > 1.0:
        return -1.0
    D = 2 * arb(hmin).sqrt().asin()
    return max(0.0, fdown(D))


def remove_arc(lo, hi, fa, fb):
    """remove the open arc (fa, fb) (floats, already shrunk) mod 2pi from [lo, hi]."""
    for rep in range(2):
        for sh in (-1, 0, 1):
            # shifted arc, shrunk outward-safely
            a = fup(arb(fa) + sh * TWOPI)
            b = fdown(arb(fb) + sh * TWOPI)
            if a < lo and b > lo:
                lo = b
            if a < hi and b > hi:
                hi = a
            if lo > hi:
                return lo, hi, False
    return lo, hi, True


def radial_forbidden(sj0, sj1, cm):
    u = -math.inf
    v = math.inf
    for sj in (sj0, sj1):
        sj = arb(sj)
        cma = arb(cm)
        disc = 4 - sj * sj * (1 - cma * cma)
        if not (disc > 0):
            return 0.0, -1.0
        r = disc.sqrt()
        r1 = fup(sj * cma - r)
        r2 = fdown(sj * cma + r)
        u = max(u, r1)
        v = min(v, r2)
    return u, v


def capacity(c, arcs, need):
    """exact rational greedy on (already outward-shrunk) float arcs; 2pi replaced by a
    rational upper bound, delta_B by a rational lower bound."""
    TP_hi = Fraction(fup(TWOPI))
    TP_lo = Fraction(fdown(TWOPI))
    db = Fraction(fdown(c.dB))
    n = len(arcs)
    if n == 0:
        cnt = 0
        x = Fraction(0)
        while x <= TP_hi - db:
            cnt += 1
            x += db
        return cnt
    # Work on the unrolled line.  Normalise each arc start into [0, TP) using the
    # *lower* 2pi for subtraction would move arcs; instead we replicate arcs with shifts
    # by both TP_lo and TP_hi (shrinking them so that both placements are covered).
    # Simpler sound approach: candidate start points = every arc end (and 0); for a
    # given start x0 place greedily on [x0, x0 + TP_hi - db] avoiding the arcs shifted
    # by j*2pi, where each shifted copy is shrunk by |j|*(TP_hi-TP_lo) on both sides.
    A = [(Fraction(a), Fraction(b)) for (a, b) in arcs]
    gap = TP_hi - TP_lo

    def shifted(j):
        out = []
        for (a, b) in A:
            a2 = a + j * TP_lo + abs(j) * gap
            b2 = b + j * TP_lo - abs(j) * gap
            if j > 0:
                a2 = a + j * TP_hi
                b2 = b + j * TP_lo
            elif j < 0:
                a2 = a + j * TP_lo
                b2 = b + j * TP_hi
            if b2 > a2:
                out.append((a2, b2))
        return out
    allarcs = []
    for j in range(-2, 4):
        allarcs.extend(shifted(j))

    def blocked(x):
        for (a, b) in allarcs:
            if a < x < b:
                return b
        return None

    starts = [b for (a, b) in A]
    best = 0
    for x0 in starts:
        if blocked(x0) is not None:
            continue
        cnt = 1
        x = x0
        limit = x0 + TP_hi - db
        while True:
            x = x + db
            while True:
                nb = blocked(x)
                if nb is None:
                    break
                x = nb
            if x > limit:
                break
            cnt += 1
            if cnt > 40:
                break
        best = max(best, cnt)
        if best >= need:
            return best
    return best


def check_node_arb(Bin, k, m, rho, RM, c=None):
    """Rigorous re-implementation of bnb2.check_node2.  Returns (code, B)."""
    if c is None:
        c = Ctx(rho)
    B = [list(map(float, row)) for row in Bin]
    for it in range(10):
        changed = False
        for i in range(1, k):
            if B[i][1] > B[0][1]:
                B[i][1] = B[0][1]
            if B[0][0] < B[i][0]:
                B[0][0] = B[i][0]
        if B[0][0] < RM[k]:
            B[0][0] = RM[k]
        for i in range(2, k):
            if B[i][2] < B[i - 1][2]:
                B[i][2] = B[i - 1][2]
        for i in range(k - 2, 0, -1):
            if B[i][3] > B[i + 1][3]:
                B[i][3] = B[i + 1][3]
        if k >= 3:
            t = fup(TWOPI - arb(B[k - 1][2]))
            if B[1][3] > t:
                B[1][3] = t
            t = fup(TWOPI - arb(B[1][2]))
            if B[k - 1][3] > t:
                B[k - 1][3] = t
        for n in range(2, k + 1):
            cnt = sum(1 for i in range(k) if B[i][1] < RM[n])
            if cnt >= n:
                return 1, B
            if cnt == n - 1:
                for i in range(k):
                    if B[i][1] >= RM[n] and B[i][0] < RM[n]:
                        B[i][0] = RM[n]
                        changed = True
        for i in range(k):
            if B[i][0] > B[i][1] or B[i][2] > B[i][3]:
                return 1, B
        for i in range(k):
            for j in range(i + 1, k):
                Bi, Bj = B[i], B[j]
                # exact enclosure of the angle-difference interval
                dlo = fdown(arb(Bi[2]) - arb(Bj[3]))
                dhi = fup(arb(Bi[3]) - arb(Bj[2]))
                cm = cos_min_ub(dlo, dhi)
                best = None
                for si in (Bi[0], Bi[1]):
                    for sj in (Bj[0], Bj[1]):
                        v = arb(si) ** 2 + arb(sj) ** 2 - 2 * arb(si) * arb(sj) * arb(cm)
                        u = fup(v)
                        best = u if best is None else max(best, u)
                if best < 4.0:
                    return 2, B
                D = min_ang_sep_lb(Bi[0], Bi[1], Bj[0], Bj[1])
                if D < 0:
                    return 2, B
                if D > 0:
                    if Bj[3] - Bj[2] < 2 * D:
                        fa = fup(arb(Bj[3]) - arb(D))
                        fb = fdown(arb(Bj[2]) + arb(D))
                        lo, hi, ok = remove_arc(Bi[2], Bi[3], fa, fb)
                        if not ok:
                            return 3, B
                        if lo > Bi[2] + 1e-12 or hi < Bi[3] - 1e-12:
                            changed = True
                        Bi[2], Bi[3] = lo, hi
                    if Bi[3] - Bi[2] < 2 * D:
                        fa = fup(arb(Bi[3]) - arb(D))
                        fb = fdown(arb(Bi[2]) + arb(D))
                        lo, hi, ok = remove_arc(Bj[2], Bj[3], fa, fb)
                        if not ok:
                            return 3, B
                        if lo > Bj[2] + 1e-12 or hi < Bj[3] - 1e-12:
                            changed = True
                        Bj[2], Bj[3] = lo, hi
                dlo = fdown(arb(Bi[2]) - arb(Bj[3]))
                dhi = fup(arb(Bi[3]) - arb(Bj[2]))
                cm = cos_min_ub(dlo, dhi)
                for (a, b) in ((Bi, Bj), (Bj, Bi)):
                    u, v = radial_forbidden(b[0], b[1], cm)
                    if u < v:
                        lo, hi = a[0], a[1]
                        if u < lo and v > lo:
                            lo = v
                        if u < hi and v > hi:
                            hi = u
                        if lo > hi:
                            return 4, B
                        if lo > a[0] + 1e-12 or hi < a[1] - 1e-12:
                            changed = True
                        a[0], a[1] = lo, hi
        if not changed:
            break
    # excess bound
    ex = arb(0)
    for i in range(k):
        th = theta_ball(c, B[i][0])
        if th is None:
            continue
        e = 2 * th - c.dB
        if e > 0:
            ex += e
        elif not (e < 0):
            ex += arb(0)   # could be either sign: contributes >= 0, ignore (sound)
    slack = TWOPI - m * c.dB
    if ex > slack:
        return 5, B
    # capacity
    arcs = []
    for i in range(k):
        th = theta_ball(c, B[i][0])
        if th is None:
            continue
        thl = arb(max(0.0, fdown(th)))
        if B[i][3] - B[i][2] < 2 * float(thl.mid()) - 1e-15:
            a = fup(arb(B[i][3]) - thl)
            b = fdown(arb(B[i][2]) + thl)
            if b > a:
                arcs.append((a, b))
    cap = capacity(c, arcs, m)
    if cap < m:
        return 6, B
    return 0, B
