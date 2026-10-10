"""
Fully rigorous re-run of the branch-and-bound: every removal decision (prune or
contraction) is certified in arb ball arithmetic (python-flint) / exact rationals.

A cheap float evaluation is used only as a FILTER: if the float value says that an action
(prune / contraction) is clearly impossible, the action is skipped, which is always
sound (a box is only ever kept, never removed, on the basis of float arithmetic).
Every action that removes anything is re-derived rigorously before it is applied.

usage: python arb_bnb.py RHO K [--tol T] [--workers W] [--ntasks N] [--out file]
"""
import sys, os, math, time, json, argparse
from fractions import Fraction
import numpy as np
from flint import arb, ctx

ctx.prec = 96
PI = arb.pi()
TWOPI = 2 * PI
TWOPI_F = 2 * math.pi

RM_F = [0.0, 0.0, 1.0, 2.0 / math.sqrt(3.0), math.sqrt(2.0), 1.0 / math.sin(math.pi / 5.0),
        2.0, 2.0, 2.30476, 2.61312, 2.81302, 2.92380]
# rigorous lower bounds for r_n (rounded down; the exact values are 2/sqrt3, sqrt2,
# 1/sin36 = 1.70130161..; the others are given decimals that are already lower bounds)
RM = [x - 1e-9 for x in RM_F] + [0.0, 0.0, 0.0, 0.0]
RM[0] = 0.0
RM[1] = 0.0


def fdown(x):
    lo = x.lower()
    f = float(lo)
    while not (arb(f) <= lo):
        f = float(np.nextafter(f, -np.inf))
    return f


def fup(x):
    hi = x.upper()
    f = float(hi)
    while not (arb(f) >= hi):
        f = float(np.nextafter(f, np.inf))
    return f


class Ctx:
    def __init__(self, rho, k):
        self.rho_f = rho
        self.k = k
        self.m = 15 - k
        self.rho = arb(rho)
        self.rho_m2 = self.rho - 2
        self.rho_m2_f = rho - 2.0
        self.dB = 2 * (1 / self.rho).asin()
        self.dB_lo = fdown(self.dB)
        self.RI = (self.rho * self.rho - 4).sqrt()
        self.RI_hi = fup(self.RI)
        self.slack = TWOPI - self.m * self.dB
        self.TP_hi = Fraction(fup(TWOPI))
        self.TP_lo = Fraction(fdown(TWOPI))
        self.db_q = Fraction(self.dB_lo)
        self.th_cache = {}
        from core import excess_lemma_margin
        self.use_excess = (self.m >= 1) and excess_lemma_margin(rho)[0] > 0.0

    def theta(self, s):
        """arb ball for theta(s), or None if s <= rho - 2 cannot be excluded"""
        r = self.th_cache.get(s)
        if r is not None or s in self.th_cache:
            return r
        sa = arb(s)
        a = sa - self.rho_m2
        if not (a > 0):
            r = None
        else:
            x = a * (2 + self.rho - sa) / (4 * self.rho * sa)
            r = 2 * x.sqrt().asin()
        if len(self.th_cache) > 200000:
            self.th_cache.clear()
        self.th_cache[s] = r
        return r


# ---------------------------------------------------------------- float filters
def theta_float(s, rho, rho_m2):
    a = s - rho_m2
    if a <= 0.0:
        return 0.0
    x = a * (2.0 + rho - s) / (4.0 * rho * s)
    if x >= 1.0:
        return math.pi
    return 2.0 * math.asin(math.sqrt(x))


def cosmin_float(dlo, dhi):
    if dhi - dlo >= TWOPI_F:
        return -1.0
    n = math.ceil((dlo - math.pi) / TWOPI_F)
    if math.pi + TWOPI_F * n <= dhi:
        return -1.0
    return min(math.cos(dlo), math.cos(dhi))


# ---------------------------------------------------------------- rigorous pieces
def cosmin_rig(lo_i, hi_i, lo_j, hi_j):
    """float lower bound of min cos(t) over t in [lo_i - hi_j, hi_i - lo_j]"""
    dl = arb(lo_i) - arb(hi_j)
    dh = arb(hi_i) - arb(lo_j)
    dlo = fdown(dl)
    dhi = fup(dh)
    if dhi - dlo >= 6.2:
        return -1.0
    n = math.ceil((dlo - math.pi) / TWOPI_F) - 1
    for nn in (n, n + 1, n + 2):
        t = PI + TWOPI * nn
        if not (t < arb(dlo)) and not (t > arb(dhi)):
            return -1.0
    return min(fdown(arb(dlo).cos()), fdown(arb(dhi).cos()))


def maxdist2_rig_lt4(Bi, Bj):
    """True only if max |Pi-Pj|^2 over the box pair is certainly < 4"""
    cm = arb(cosmin_rig(Bi[2], Bi[3], Bj[2], Bj[3]))
    for si in (Bi[0], Bi[1]):
        for sj in (Bj[0], Bj[1]):
            a = arb(si)
            b = arb(sj)
            v = a * a + b * b - 2 * a * b * cm
            if not (v < 4):
                return False
    return True


def hmin_corners_float(a0, a1, b0, b1):
    hmin = 1e300
    for si in (a0, a1):
        for sj in (b0, b1):
            d = si - sj
            num = 4.0 - d * d
            den = 4.0 * si * sj
            if den <= 0.0:
                h = 1e300 if num > 0.0 else -1e300
            else:
                h = num / den
            hmin = min(hmin, h)
    return hmin


def angsep_rig(a0, a1, b0, b1):
    """rigorous float lower bound D for the circular angle; -1 if certainly infeasible."""
    hmin = math.inf
    for si in (a0, a1):
        for sj in (b0, b1):
            sa = arb(si)
            sb = arb(sj)
            d = sa - sb
            num = 4 - d * d
            if si == 0.0 or sj == 0.0:
                h = math.inf if (num > 0) else -math.inf
            else:
                h = fdown(num / (4 * sa * sb))
            hmin = min(hmin, h)
    if hmin <= 0.0:
        return 0.0
    if hmin > 1.0:
        return -1.0
    return max(0.0, fdown(2 * arb(hmin).sqrt().asin()))


def remove_arc_rig(lo, hi, faA, fbA):
    """remove the open arc (faA, fbA) (arb balls; the certainly-forbidden part is
    (faA.upper, fbA.lower)) and its 2pi-translates from [lo, hi]."""
    for rep in range(2):
        for sh in (-1, 0, 1):
            a = fup(faA + sh * TWOPI)
            b = fdown(fbA + sh * TWOPI)
            if not (b > a):
                continue
            if a < lo and b > lo:
                lo = b
            if a < hi and b > hi:
                hi = a
            if lo > hi:
                return lo, hi, False
    return lo, hi, True


def radial_rig(sj0, sj1, cm):
    u = -math.inf
    v = math.inf
    cma = arb(cm)
    for sj in (sj0, sj1):
        s = arb(sj)
        disc = 4 - s * s * (1 - cma * cma)
        if not (disc > 0):
            return 0.0, -1.0
        r = disc.sqrt()
        u = max(u, fup(s * cma - r))
        v = min(v, fdown(s * cma + r))
    return u, v


def capacity_rig(c, arcs, need):
    """exact-rational greedy; arcs = list of (a, b) floats, already certainly-forbidden."""
    n = len(arcs)
    db = c.db_q
    TP_hi, TP_lo = c.TP_hi, c.TP_lo
    if n == 0:
        cnt = 0
        x = Fraction(0)
        while x <= TP_hi - db:
            cnt += 1
            x += db
        return cnt
    A = [(Fraction(a), Fraction(b)) for (a, b) in arcs]
    allarcs = []
    for j in range(-2, 4):
        for (a, b) in A:
            if j > 0:
                a2, b2 = a + j * TP_hi, b + j * TP_lo
            elif j < 0:
                a2, b2 = a + j * TP_lo, b + j * TP_hi
            else:
                a2, b2 = a, b
            if b2 > a2:
                allarcs.append((a2, b2))

    def bump(x):
        moved = True
        while moved:
            moved = False
            for (a, b) in allarcs:
                if a < x < b:
                    x = b
                    moved = True
        return x
    best = 0
    for (a0, b0) in A:
        x0 = b0
        if bump(x0) != x0:
            continue
        cnt = 1
        x = x0
        limit = x0 + TP_hi - db
        while True:
            x = bump(x + db)
            if x > limit:
                break
            cnt += 1
            if cnt > 40:
                break
        best = max(best, cnt)
        if best >= need:
            return best
    return best


# ---------------------------------------------------------------- node test
FILT = 1e-6   # float filter width (an action is examined rigorously if within FILT)


def check_node_rig(B, c):
    k, m = c.k, c.m
    rho, rho_m2 = c.rho_f, c.rho_m2_f
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
            cnt = 0
            for i in range(k):
                if B[i][1] < RM[n]:
                    cnt += 1
            if cnt >= n:
                return 1
            if cnt == n - 1:
                for i in range(k):
                    if B[i][1] >= RM[n] and B[i][0] < RM[n]:
                        B[i][0] = RM[n]
                        changed = True
        for i in range(k):
            if B[i][0] > B[i][1] or B[i][2] > B[i][3]:
                return 1
        for i in range(k):
            Bi = B[i]
            for j in range(i + 1, k):
                Bj = B[j]
                # --- R2 max distance (float filter, rigorous confirm)
                cmf = cosmin_float(Bi[2] - Bj[3], Bi[3] - Bj[2])
                mdf = -1.0
                for si in (Bi[0], Bi[1]):
                    for sj in (Bj[0], Bj[1]):
                        v = si * si + sj * sj - 2.0 * si * sj * cmf
                        if v > mdf:
                            mdf = v
                if mdf < 4.0 + FILT:
                    if maxdist2_rig_lt4(Bi, Bj):
                        return 2
                # --- R3 angular exclusion
                hf = hmin_corners_float(Bi[0], Bi[1], Bj[0], Bj[1])
                if hf > 1.0 + FILT:
                    D = angsep_rig(Bi[0], Bi[1], Bj[0], Bj[1])
                    if D < 0:
                        return 2
                if hf > FILT:
                    Df = 2.0 * math.asin(math.sqrt(min(hf, 1.0)))
                    for (a, b) in ((Bi, Bj), (Bj, Bi)):
                        # arc forbidden for a: (b_hi - D, b_lo + D)
                        if b[3] - b[2] < 2.0 * Df + FILT:
                            fa = b[3] - Df
                            fb = b[2] + Df
                            hit = False
                            for sh in (-TWOPI_F, 0.0, TWOPI_F):
                                if (fa + sh < a[2] + FILT and fb + sh > a[2] - FILT) or \
                                   (fa + sh < a[3] + FILT and fb + sh > a[3] - FILT):
                                    hit = True
                            if hit:
                                D = angsep_rig(Bi[0], Bi[1], Bj[0], Bj[1])
                                if D < 0:
                                    return 2
                                if D > 0:
                                    DA = arb(D)
                                    lo, hi, ok = remove_arc_rig(a[2], a[3], arb(b[3]) - DA,
                                                                arb(b[2]) + DA)
                                    if not ok:
                                        return 3
                                    if lo > a[2] + 1e-12 or hi < a[3] - 1e-12:
                                        changed = True
                                    a[2], a[3] = lo, hi
                # --- R4 radial exclusion
                cmf = cosmin_float(Bi[2] - Bj[3], Bi[3] - Bj[2])
                for (a, b) in ((Bi, Bj), (Bj, Bi)):
                    # float filter
                    u = -1e300
                    v = 1e300
                    ok = True
                    for sj in (b[0], b[1]):
                        disc = 4.0 - sj * sj * (1.0 - cmf * cmf)
                        if disc <= 0.0:
                            ok = False
                            break
                        r = math.sqrt(disc)
                        u = max(u, sj * cmf - r)
                        v = min(v, sj * cmf + r)
                    if not ok or u >= v:
                        continue
                    if (u < a[0] + FILT and v > a[0] - FILT) or (u < a[1] + FILT and v > a[1] - FILT):
                        cm = cosmin_rig(Bi[2], Bi[3], Bj[2], Bj[3])
                        ur, vr = radial_rig(b[0], b[1], cm)
                        if ur < vr:
                            lo, hi = a[0], a[1]
                            if ur < lo and vr > lo:
                                lo = vr
                            if ur < hi and vr > hi:
                                hi = ur
                            if lo > hi:
                                return 4
                            if lo > a[0] + 1e-12 or hi < a[1] - 1e-12:
                                changed = True
                            a[0], a[1] = lo, hi
        if not changed:
            break
    # --- R5 excess (float filter, rigorous confirm)
    exf = 0.0
    for i in range(k):
        th = theta_float(B[i][0], rho, rho_m2)
        e = 2.0 * th - c.dB_lo
        if e > 0.0:
            exf += e
    slack_f = TWOPI_F - m * c.dB_lo
    if c.use_excess and exf > slack_f - FILT:
        ex = arb(0)
        for i in range(k):
            th = c.theta(B[i][0])
            if th is None:
                continue
            e = 2 * th - c.dB
            if e > 0:
                ex += e
        if ex > c.slack:
            return 5
    # --- R6 capacity (float filter with enlarged arcs, rigorous confirm)
    arcs_f = []
    for i in range(k):
        th = theta_float(B[i][0], rho, rho_m2)
        if th > 0.0:
            w = B[i][3] - B[i][2]
            if w < 2.0 * th + FILT:
                arcs_f.append((B[i][3] - th - FILT, B[i][2] + th + FILT))
    if not arcs_f:
        return 0
    # float pre-filter: capacity with ENLARGED arcs and enlarged delta (a lower bound
    # direction); if even that leaves >= m points, the rigorous bound cannot prune.
    from core import capacity_ub
    aa = np.array([x[0] for x in arcs_f] + [0.0])
    bb = np.array([x[1] for x in arcs_f] + [0.0])
    capf = capacity_ub(aa, bb, len(arcs_f), c.dB_lo + FILT, m)
    if capf >= m:
        return 0
    arcs = []
    for i in range(k):
        th = c.theta(B[i][0])
        if th is None:
            continue
        thl = fdown(th)
        if thl <= 0.0:
            continue
        a = fup(arb(B[i][3]) - arb(thl))
        b = fdown(arb(B[i][2]) + arb(thl))
        if b > a:
            arcs.append((a, b))
    cap = capacity_rig(c, arcs, m)
    if cap < m:
        return 6
    return 0


def choose_split(B, k):
    best = -1.0
    bi = bd = -1
    for i in range(k):
        ws = B[i][1] - B[i][0]
        wa = (B[i][3] - B[i][2]) * B[i][1]
        if ws > best:
            best, bi, bd = ws, i, 0
        if wa > best:
            best, bi, bd = wa, i, 2
    return best, bi, bd


def root_box(c):
    k = c.k
    B = [[0.0, c.RI_hi, 0.0, fup(TWOPI)] for i in range(k)]
    B[0] = [RM[k], c.RI_hi, 0.0, 0.0]
    return B


def dfs(c, stack, tol, max_nodes=10 ** 12):
    nodes = 0
    stats = [0] * 8
    surv = []
    while stack and nodes < max_nodes:
        B, v = stack.pop()
        nodes += 1
        code = check_node_rig(B, c)
        stats[code] += 1
        if code != 0:
            continue
        best, bi, bd = choose_split(B, c.k)
        if best < tol:
            surv.append(B)
            stats[7] += 1
            continue
        mid = 0.5 * (B[bi][bd] + B[bi][bd + 1])
        B1 = [row[:] for row in B]
        B2 = [row[:] for row in B]
        B1[bi][bd + 1] = mid
        B2[bi][bd] = mid
        stack.append((B1, v / 2))
        stack.append((B2, v / 2))
    return nodes, stats, surv, stack


G = {}


def set_no_rm(flag):
    if flag:
        for i in range(len(RM)):
            RM[i] = 0.0


def winit(rho, k, tol, no_rm=False):
    set_no_rm(no_rm)
    G["c"] = Ctx(rho, k)
    G["tol"] = tol


def wtask(boxes):
    t0 = time.time()
    nodes, stats, surv, rest = dfs(G["c"], [(b, v) for (b, v) in boxes], G["tol"])
    return nodes, stats, surv, time.time() - t0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("rho", type=float)
    ap.add_argument("k", type=int)
    ap.add_argument("--tol", type=float, default=1e-4)
    ap.add_argument("--workers", type=int, default=3)
    ap.add_argument("--ntasks", type=int, default=400)
    ap.add_argument("--out", type=str, default="")
    ap.add_argument("--no-rm", action="store_true", help="do not use the r_n bounds (F4)")
    a = ap.parse_args()
    assert a.workers <= 4
    set_no_rm(a.no_rm)
    c = Ctx(a.rho, a.k)
    t0 = time.time()
    # breadth-first split of the root in the main process
    from collections import deque
    q = deque([(root_box(c), 1.0)])
    nodes = 0
    stats = [0] * 8
    surv = []
    while q and len(q) < a.ntasks:
        B, v = q.popleft()
        nodes += 1
        code = check_node_rig(B, c)
        stats[code] += 1
        if code != 0:
            continue
        best, bi, bd = choose_split(B, c.k)
        if best < a.tol:
            surv.append(B)
            stats[7] += 1
            continue
        mid = 0.5 * (B[bi][bd] + B[bi][bd + 1])
        B1 = [row[:] for row in B]; B2 = [row[:] for row in B]
        B1[bi][bd + 1] = mid; B2[bi][bd] = mid
        q.append((B1, v / 2)); q.append((B2, v / 2))
    tasks = [[x] for x in q]
    from multiprocessing import Pool
    done_tasks = 0
    with Pool(a.workers, initializer=winit, initargs=(a.rho, a.k, a.tol, a.no_rm)) as pool:
        for n, st, sv, dt in pool.imap_unordered(wtask, tasks):
            nodes += n
            stats = [x + y for x, y in zip(stats, st)]
            surv.extend(sv)
            done_tasks += 1
            if done_tasks % 20 == 0 or done_tasks == len(tasks):
                print(f"  tasks {done_tasks}/{len(tasks)} nodes={nodes} survivors={len(surv)} "
                      f"elapsed={time.time()-t0:.0f}s", flush=True)
    names = ["alive", "order", "dist", "ang", "rad", "excess", "cap", "tol_survivor"]
    res = dict(rho=a.rho, k=a.k, tol=a.tol, use_F4=not a.no_rm, nodes=nodes, survivors=len(surv),
               stats=dict(zip(names, stats)), time_s=time.time() - t0, arithmetic="arb+exact rationals")
    print(json.dumps(res))
    if a.out:
        res["survivor_boxes"] = surv
        json.dump(res, open(a.out, "w"))


if __name__ == "__main__":
    main()
