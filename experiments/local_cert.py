"""Rigorous local certificate for a jammed packing (points in the unit disk, maximise d = min distance).

Given an approximate configuration x~ (from known_packings JSON) with boundary set B and contact set C,
|B| + |C| = 2n, this script proves with arb ball arithmetic (python-flint):

 (1) EXISTENCE/UNIQUENESS: the system  |p_i|^2 = 1 (i in B), |p_i-p_j|^2 = t ((i,j) in C), y_g = 0 (gauge)
     has a unique solution z* = (x*, t*) in an explicit box Z (Krawczyk test).
 (2) FEASIBILITY: for every z in Z, all inactive constraints hold strictly (|p_i| < 1 for i not in B,
     |p_i - p_j|^2 > t for non-contacts).  Hence x* is a packing with min distance sqrt(t*).
 (3) KKT: there are unique multipliers lambda_k (contacts, sum = 1) and mu_i (boundary) with
        sum_j lambda_ij (p_i - p_j) = mu_i p_i  for every i,
     all STRICTLY POSITIVE (enclosures computed for every z in Z).
 (4) RANK: sigma := a rigorous lower bound for the smallest singular value of L restricted to (J x*)^perp,
     where L is the 2n x 2n matrix of linearised active constraints (rows a_k, b_i) and J x* the rotation field.
 (5) LOCAL UNIQUENESS RADIUS: delta_loc = sigma / K with
        K^2 = sum_k 4 max(1, 1/lambda_k)^2 + sum_i (2/mu_i + 1)^2.
     LEMMA: if x is any n-point configuration in the closed unit disk with min distance >= sqrt(t*) and
     the optimally rotated displacement delta = R x - x* satisfies |delta|_2 < delta_loc, then delta = 0.
     (Proof in proof_attempt.md / lemmas.md, "Local uniqueness lemma".)

Usage: python local_cert.py n [prec_bits]
"""
import sys, os, json
import mpmath as mp
from flint import arb, arb_mat, ctx

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)


def load(n):
    with open(os.path.join(ROOT, "known_packings", "known_packings_13_20.json")) as f:
        D = json.load(f)[str(n)]
    pts = [(mp.mpf(a), mp.mpf(b)) for a, b in D["points"]]
    return pts, mp.mpf(D["d"]), D["boundary"], [tuple(c) for c in D["contacts"]]


def rotate_gauge(pts, g):
    ang = mp.atan2(pts[g][1], pts[g][0])
    c, s = mp.cos(-ang), mp.sin(-ang)
    return [(c * x - s * y, s * x + c * y) for x, y in pts]


def A(x):  # mp -> exact arb (midpoint) via string
    return arb(mp.nstr(x, mp.mp.dps + 5))


def F_and_J(z, n, B, C, g):
    """Residual F(z) and Jacobian J(z) as python lists of arb (z: list of arb, length 2n+1)."""
    m = len(B) + len(C) + 1
    N = 2 * n + 1
    F = [arb(0)] * m
    J = [[arb(0)] * N for _ in range(m)]
    k = 0
    for i in B:
        x, y = z[2 * i], z[2 * i + 1]
        F[k] = x * x + y * y - 1
        J[k][2 * i] = 2 * x; J[k][2 * i + 1] = 2 * y
        k += 1
    for (i, j) in C:
        dx, dy = z[2 * i] - z[2 * j], z[2 * i + 1] - z[2 * j + 1]
        F[k] = dx * dx + dy * dy - z[N - 1]
        J[k][2 * i] = 2 * dx; J[k][2 * i + 1] = 2 * dy
        J[k][2 * j] = -2 * dx; J[k][2 * j + 1] = -2 * dy
        J[k][N - 1] = arb(-1)
        k += 1
    F[k] = z[2 * g + 1]
    J[k][2 * g + 1] = arb(1)
    return F, J


def ball(mid, rad):
    return arb(mid, rad)


def main(n, prec=256):
    ctx.prec = prec
    mp.mp.dps = int(prec * 0.30)
    pts, d, B, C = load(n)
    assert len(B) + len(C) == 2 * n, (len(B), len(C))
    g = B[0]
    pts = rotate_gauge(pts, g)
    N = 2 * n + 1
    # Newton polish in mp to full precision
    z = []
    for x, y in pts:
        z += [x, y]
    z.append(d * d)
    for it in range(8):
        za = [A(v) for v in z]
        F, J = F_and_J(za, n, B, C, g)
        Fm = mp.matrix([[F[k].mid().str(mp.mp.dps, radius=False) if False else mp.mpf(F[k].mid().str(mp.mp.dps, radius=False))] for k in range(N)])
        Jm = mp.matrix([[mp.mpf(J[r][c].mid().str(mp.mp.dps, radius=False)) for c in range(N)] for r in range(N)])
        dz = mp.lu_solve(Jm, Fm)
        z = [z[q] - dz[q] for q in range(N)]
        res = max(abs(v) for v in Fm)
    print(f"n={n}: Newton residual {mp.nstr(res, 5)}")
    zt = [A(v) for v in z]  # exact midpoint
    # Krawczyk
    F0, J0 = F_and_J(zt, n, B, C, g)
    Jmid = mp.matrix([[mp.mpf(J0[r][c].mid().str(mp.mp.dps, radius=False)) for c in range(N)] for r in range(N)])
    Ym = mp.inverse(Jmid)
    Y = arb_mat([[A(Ym[r, c]) for c in range(N)] for r in range(N)])
    rad = arb(10) ** (-(int(prec * 0.30) // 2))
    Z = [arb(zt[q].mid(), rad) for q in range(N)]
    FZ, JZ = F_and_J(Z, n, B, C, g)
    Fv = arb_mat([[F0[k]] for k in range(N)])
    JZm = arb_mat(JZ)
    Iden = arb_mat([[arb(1) if r == c else arb(0) for c in range(N)] for r in range(N)])
    dZ = arb_mat([[Z[q] - zt[q]] for q in range(N)])
    K = arb_mat([[zt[q]] for q in range(N)]) - Y * Fv + (Iden - Y * JZm) * dZ
    ok = True
    for q in range(N):
        kq = K[q, 0]
        lo, hi = kq.mid() - kq.rad(), kq.mid() + kq.rad()
        if not (lo > Z[q].mid() - Z[q].rad() and hi < Z[q].mid() + Z[q].rad()):
            ok = False
    print(f"  Krawczyk K(Z) in int(Z): {ok}   (box radius {rad})")
    if not ok:
        return None
    # use K (tighter) intersected: just use Z as the enclosure
    P = [(Z[2 * i], Z[2 * i + 1]) for i in range(n)]
    t = Z[N - 1]
    dlo = t.sqrt()
    print(f"  d* in {dlo.str(40)}")
    print(f"  t* = d*^2 in {t.str(40)}")
    # (2) inactive constraints
    Cset = set(C)
    min_gap = None
    for i in range(n):
        for j in range(i + 1, n):
            if (i, j) in Cset:
                continue
            dx, dy = P[i][0] - P[j][0], P[i][1] - P[j][1]
            s = dx * dx + dy * dy - t
            if not (s > 0):
                print("  inactive pair FAIL", i, j, s)
                ok = False
            v = s.mid() - s.rad()
            min_gap = v if min_gap is None or v < min_gap else min_gap
    min_bslack = None
    for i in range(n):
        if i in B:
            continue
        s = 1 - (P[i][0] * P[i][0] + P[i][1] * P[i][1])
        if not (s > 0):
            print("  inactive boundary FAIL", i, s); ok = False
        v = s.mid() - s.rad()
        min_bslack = v if min_bslack is None or v < min_bslack else min_bslack
    print(f"  inactive constraints strict: {ok}; min dist^2 slack > {min_gap}, min boundary slack > {min_bslack}")
    # (3) multipliers: unknowns lambda (|C|), mu (|B|); equations: equilibrium (2n) minus one x-eq at point m with y_m != 0, plus sum lambda = 1
    nl, nm = len(C), len(B)
    # choose m: a point with |y| clearly nonzero
    mrow = max(range(n), key=lambda i: abs(float(P[i][1].mid())))
    assert not P[mrow][1].contains(0), "torque argument needs y_m != 0"   # rigorous: ball excludes 0
    rows = []
    rhs = []
    for i in range(n):
        for comp in (0, 1):
            if i == mrow and comp == 0:
                continue
            row = [arb(0)] * (nl + nm)
            for kk, (a, b) in enumerate(C):
                if a == i:
                    row[kk] = P[i][comp] - P[b][comp]
                elif b == i:
                    row[kk] = P[i][comp] - P[a][comp]
            if i in B:
                row[nl + B.index(i)] = -P[i][comp]
            rows.append(row); rhs.append(arb(0))
    rows.append([arb(1)] * nl + [arb(0)] * nm); rhs.append(arb(1))
    M = arb_mat(rows)
    sol = M.solve(arb_mat([[r] for r in rhs]))
    lam = [sol[k, 0] for k in range(nl)]
    mu = [sol[nl + k, 0] for k in range(nm)]
    pos = all(l > 0 for l in lam) and all(u > 0 for u in mu)
    lmin = min(l.mid() - l.rad() for l in lam)
    mumin = min(u.mid() - u.rad() for u in mu)
    print(f"  multipliers strictly positive: {pos};  min lambda > {lmin}, min mu > {mumin}")
    print(f"   (y_m at dropped equation point {mrow}: {P[mrow][1].str(10)})")
    ok = ok and pos
    # (4) sigma: L rows (2n x 2n) evaluated on Z; L'^T L' = L^T L + u u^T, u = Jx/|Jx|; lower bound on lambda_min via Cholesky
    n2 = 2 * n
    Lr = []
    for (i, j) in C:
        r = [arb(0)] * n2
        for comp in (0, 1):
            r[2 * i + comp] = 2 * (P[i][comp] - P[j][comp])
            r[2 * j + comp] = -2 * (P[i][comp] - P[j][comp])
        Lr.append(r)
    for i in B:
        r = [arb(0)] * n2
        for comp in (0, 1):
            r[2 * i + comp] = -2 * P[i][comp]
        Lr.append(r)
    Lm = arb_mat(Lr)
    Jx = []
    for i in range(n):
        Jx += [-P[i][1], P[i][0]]
    nrm = sum((v * v for v in Jx), arb(0)).sqrt()
    u = [v / nrm for v in Jx]
    G = Lm.transpose() * Lm + arb_mat([[u[a] * u[b] for b in range(n2)] for a in range(n2)])
    # approximate min eigenvalue
    import numpy as np
    Gf = np.array([[float(G[a, b].mid()) for b in range(n2)] for a in range(n2)])
    ev = np.linalg.eigvalsh(Gf)
    tau = arb(float(ev[0]) * 0.98)
    # interval Cholesky of G - tau I
    Ach = [[G[a, b] - (tau if a == b else 0) for b in range(n2)] for a in range(n2)]
    Lc = [[arb(0)] * n2 for _ in range(n2)]
    pd = True
    for a in range(n2):
        s = Ach[a][a] - sum((Lc[a][q] * Lc[a][q] for q in range(a)), arb(0))
        if not (s > 0):
            pd = False; break
        Lc[a][a] = s.sqrt()
        for b in range(a + 1, n2):
            s2 = Ach[b][a] - sum((Lc[b][q] * Lc[a][q] for q in range(a)), arb(0))
            Lc[b][a] = s2 / Lc[a][a]
    sigma = tau.sqrt()
    print(f"  L'^T L' - tau I positive definite: {pd};  sigma >= {sigma.str(10)}  (float eigs min {ev[0]:.6g}, next {ev[1]:.6g})")
    ok = ok and pd
    # (5) delta_loc
    K2 = arb(0)
    for l in lam:
        lo = arb(l.mid() - l.rad())
        f = arb(1) if lo >= 1 else 1 / lo
        K2 += 4 * f * f
    for u_ in mu:
        lo = arb(u_.mid() - u_.rad())
        K2 += (2 / lo + 1) * (2 / lo + 1)
    Kc = K2.sqrt()
    dloc = sigma / Kc
    dloc_lo = dloc.mid() - dloc.rad()
    print(f"  K = {Kc.str(8)};  delta_loc >= {dloc_lo}")
    print(f"  ALL CHECKS PASSED: {ok}")
    out = dict(n=n, ok=bool(ok), d_star=t.sqrt().str(45, radius=False), t_star_ball=t.str(50),
               box_radius=str(rad), delta_loc=str(dloc_lo), sigma=str(sigma.mid()),
               lambda_min=str(lmin), mu_min=str(mumin), gauge_point=g,
               lambdas=[l.str(15) for l in lam], mus=[u_.str(15) for u_ in mu],
               points_mid=[[P[i][0].mid().str(45, radius=False), P[i][1].mid().str(45, radius=False)] for i in range(n)],
               boundary=B, contacts=C)
    with open(os.path.join(ROOT, "known_packings", f"local_certificate_n{n}.json"), "w") as f:
        json.dump(out, f, indent=1)
    return out


if __name__ == "__main__":
    n = int(sys.argv[1])
    prec = int(sys.argv[2]) if len(sys.argv) > 2 else 256
    main(n, prec)
