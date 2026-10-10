"""Unit tests of the primitives in core.py against arb / brute force."""
import math, random, time
import numpy as np
from flint import arb, ctx
from core import (theta_f, maxdist2, min_ang_sep, capacity_ub, remove_arc, constants,
                  TWO_PI)

RHO = 3.52135696470617
RI_HI, DB_LO, RHO_M2 = constants(RHO)
rng = random.Random(12345)


def test_theta():
    ctx.prec = 120
    r = arb(RHO)
    worst = 0.0
    for t in range(20000):
        s = rng.uniform(RHO_M2, RI_HI)
        if t < 50:
            s = RHO_M2 + 10.0 ** (-rng.uniform(1, 15))
        sa = arb(s)
        c = (sa * sa + r * r - 4) / (2 * sa * r)
        th = c.acos()
        f = theta_f(s, RHO, RHO_M2)
        err = abs(f - float(th.mid()))
        worst = max(worst, err / max(float(th.mid()), 1e-300))
    print("theta_f max relative error vs arb:", worst)
    assert worst < 1e-12


def brute_maxdist2(B1, B2, n=60):
    best = 0.0
    for s1 in np.linspace(B1[0], B1[1], n):
        for p1 in np.linspace(B1[2], B1[3], n):
            P = np.array([s1 * math.cos(p1), s1 * math.sin(p1)])
            s2 = np.linspace(B2[0], B2[1], n)[:, None]
            p2 = np.linspace(B2[2], B2[3], n)[None, :]
            Q = np.stack([s2 * np.cos(p2), s2 * np.sin(p2)])
            d2 = (Q[0] - P[0]) ** 2 + (Q[1] - P[1]) ** 2
            best = max(best, d2.max())
    return best


def rand_box():
    s0 = rng.uniform(0, 2.9)
    s1 = min(2.9, s0 + rng.uniform(0, 0.8))
    p0 = rng.uniform(0, TWO_PI)
    p1 = p0 + rng.uniform(0, 1.5)
    return [s0, s1, p0, p1]


def test_maxdist2():
    worst_under = 0.0
    for t in range(300):
        B1, B2 = rand_box(), rand_box()
        f = maxdist2(*B1, *B2)
        b = brute_maxdist2(B1, B2, 25)
        assert f >= b - 1e-12, (B1, B2, f, b)
        worst_under = max(worst_under, f - b)
    print("maxdist2: never below brute force; max overestimate on grid", worst_under)


def test_min_ang_sep():
    # for random radius boxes, sample radii; any pair of radii and angle with distance>=2
    # must have angle >= D
    bad = 0
    for t in range(3000):
        a0 = rng.uniform(0, 2.9); a1 = min(2.9, a0 + rng.uniform(0, 0.5))
        b0 = rng.uniform(0, 2.9); b1 = min(2.9, b0 + rng.uniform(0, 0.5))
        D = min_ang_sep(a0, a1, b0, b1)
        for u in range(30):
            si = rng.uniform(a0, a1); sj = rng.uniform(b0, b1)
            # smallest angle with distance >= 2
            c = (si * si + sj * sj - 4) / (2 * si * sj) if si * sj > 0 else -2
            if c >= 1:
                need = 0.0
            elif c <= -1:
                need = math.pi if (si + sj) >= 2 else None
            else:
                need = math.acos(c)
            if D < 0:
                # claims infeasible: check
                if need is not None and si + sj >= 2 - 1e-12:
                    bad += 1
                continue
            if need is None:
                continue
            if need < D - 1e-12:
                bad += 1
    print("min_ang_sep violations:", bad)
    assert bad == 0


def slow_capacity(arcs, db, starts=4000):
    """independent slow implementation: try many start points (all arc ends + random) and
    place greedily on a list of allowed intervals."""
    def allowed(x):
        x %= TWO_PI
        for (a, b) in arcs:
            t = (x - a) % TWO_PI
            if 0 < t < (b - a):
                return False
        return True

    def next_allowed(x):
        # smallest y >= x that is allowed (scan arc ends)
        for _ in range(50):
            moved = False
            for (a, b) in arcs:
                t = (x - a) % TWO_PI
                if 0 < t < (b - a):
                    x = x + ((b - a) - t)
                    moved = True
            if not moved:
                return x
        return x
    cands = [b % TWO_PI for (a, b) in arcs] + [rng.uniform(0, TWO_PI) for _ in range(starts)]
    best = 0
    for st in cands:
        if not allowed(st):
            continue
        cnt = 1
        x = st
        while True:
            x = next_allowed(x + db)
            if x > st + TWO_PI - db:
                break
            cnt += 1
        best = max(best, cnt)
    return best


def test_capacity():
    db = DB_LO
    mism = 0
    for t in range(3000):
        n = rng.randint(0, 7)
        arcs = []
        for i in range(n):
            c = rng.uniform(0, TWO_PI)
            h = rng.uniform(0.01, 0.8)
            arcs.append((c - h, c + h))
        a = np.array([x[0] for x in arcs] + [0.0])
        b = np.array([x[1] for x in arcs] + [0.0])
        f = capacity_ub(a, b, n, db, 99)
        s = slow_capacity(arcs, db, 300)
        if f < s:
            print("UNSOUND", arcs, f, s)
            mism += 1
        elif f > s:
            # could be slow version missing the optimal start; recheck with more starts
            s2 = slow_capacity(arcs, db, 20000)
            if f > s2:
                print("capacity larger than found (ok if tight):", f, s2, arcs)
    print("capacity: unsound cases", mism)
    assert mism == 0


def test_remove_arc():
    for t in range(20000):
        lo = rng.uniform(0, 6); hi = lo + rng.uniform(0, 2)
        c = rng.uniform(-1, 7); h = rng.uniform(0, 2)
        nlo, nhi, ok = remove_arc(lo, hi, c - h, c + h)
        # every x in [lo,hi] not in the arc (mod 2pi) must be in [nlo,nhi] (if ok)
        for u in range(20):
            x = rng.uniform(lo, hi)
            t2 = (x - (c - h)) % TWO_PI
            inarc = 0 < t2 < 2 * h
            if not inarc:
                assert ok and nlo <= x <= nhi, (lo, hi, c, h, nlo, nhi, ok, x)
    print("remove_arc ok")


if __name__ == "__main__":
    t0 = time.time()
    print("constants: RI_HI", RI_HI, "DB_LO", DB_LO, "RHO_M2", RHO_M2)
    test_theta()
    test_maxdist2()
    test_min_ang_sep()
    test_remove_arc()
    test_capacity()
    print("all primitive tests passed in %.1fs" % (time.time() - t0))
