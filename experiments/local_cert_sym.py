"""Rigorous local certificate for a MIRROR-SYMMETRIC jammed packing whose active set is overdetermined
(|B| + |C| > 2n), e.g. n = 17.

Symmetry: reflection x -> -x maps the configuration to itself (point permutation sig, an involution).
  * Reduced unknowns: (x_i, y_i) for one representative of each 2-orbit, y_i for fixed points (x_i = 0), and t.
  * Reduced equations: one per orbit of active constraints.  If square & Krawczyk succeeds, the unique
    symmetric solution satisfies ALL original active equations exactly (by symmetry).
  * Multipliers: symmetric ones (equal on mirror pairs) from the reduced equilibrium system (square);
    all must be > 0.  They satisfy the full equilibrium equations by symmetry.
  * sigma, K, delta_loc exactly as in local_cert.py (lemma L7 holds for ANY positive multipliers satisfying
    the KKT identity and for the full linearised active matrix L).
Usage: python local_cert_sym.py n
"""
import sys, os, json, math
import mpmath as mp
import numpy as np
from flint import arb, arb_mat, ctx

HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(HERE)


def A(x):
    return arb(mp.nstr(x, mp.mp.dps + 5))


def amid(a):
    return mp.mpf(a.mid().str(mp.mp.dps, radius=False))


def main(n, prec=256):
    ctx.prec = prec; mp.mp.dps = int(prec * 0.30)
    D = json.load(open(os.path.join(ROOT, "known_packings", "known_packings_13_20.json")))[str(n)]
    pts = [(mp.mpf(a), mp.mpf(b)) for a, b in D["points"]]
    B = D["boundary"]; C = [tuple(c) for c in D["contacts"]]
    # mirror map: x -> -x
    sig = []
    for i in range(n):
        best = min(range(n), key=lambda j: (pts[j][0] + pts[i][0]) ** 2 + (pts[j][1] - pts[i][1]) ** 2)
        assert abs(pts[best][0] + pts[i][0]) + abs(pts[best][1] - pts[i][1]) < mp.mpf(10) ** -20, i
        sig.append(best)
    assert all(sig[sig[i]] == i for i in range(n))
    reps = sorted(set(min(i, sig[i]) for i in range(n)))
    var = {}   # point -> (index of x var or None, index of y var, sign)
    nv = 0
    for i in reps:
        if sig[i] == i:
            var[i] = (None, nv, 1); nv += 1
        else:
            var[i] = (nv, nv + 1, 1); var[sig[i]] = (nv, nv + 1, -1); nv += 2
    it = nv; nv += 1
    # constraint orbits
    def norm_c(c):
        a, b = c; return (min(a, b), max(a, b))
    Cset = set(C)
    corb = []
    seen = set()
    for c in C:
        if c in seen:
            continue
        m = norm_c((sig[c[0]], sig[c[1]]))
        seen.add(c); seen.add(m)
        corb.append((c, 2 if m != c else 1))
    borb = []
    seenb = set()
    for i in B:
        if i in seenb:
            continue
        seenb.add(i); seenb.add(sig[i])
        borb.append((i, 2 if sig[i] != i else 1))
    neq = len(corb) + len(borb)
    print(f"n={n}: reduced unknowns {nv}, reduced equations {neq}; |B|={len(B)} |C|={len(C)} (2n={2*n})")
    assert neq == nv, "reduced system not square"

    def coords(z, i):
        xv, yv, sg = var[i]
        x = (z[xv] * sg) if xv is not None else arb(0)
        return x, z[yv]

    def FJ(z):
        F = []; J = []
        for (i, mlt) in borb:
            x, y = coords(z, i)
            F.append(x * x + y * y - 1)
            row = [arb(0)] * nv
            xv, yv, sg = var[i]
            if xv is not None:
                row[xv] += 2 * x * sg
            row[yv] += 2 * y
            J.append(row)
        for ((i, j), mlt) in corb:
            xi, yi = coords(z, i); xj, yj = coords(z, j)
            F.append((xi - xj) * (xi - xj) + (yi - yj) * (yi - yj) - z[it])
            row = [arb(0)] * nv
            for (p, s_) in ((i, 1), (j, -1)):
                xv, yv, sg = var[p]
                if xv is not None:
                    row[xv] += 2 * (xi - xj) * s_ * sg
                row[yv] += 2 * (yi - yj) * s_
            row[it] += -1
            J.append(row)
        return F, J
    z = [None] * nv
    for i in reps:
        xv, yv, sg = var[i]
        if xv is not None:
            z[xv] = pts[i][0]
        z[yv] = pts[i][1]
    z[it] = mp.mpf(D["d"]) ** 2
    for k_ in range(8):
        F, J = FJ([A(v) for v in z])
        Fm = mp.matrix([[amid(f)] for f in F]); Jm = mp.matrix([[amid(e) for e in row] for row in J])
        dz = mp.lu_solve(Jm, Fm)
        z = [z[q] - dz[q] for q in range(nv)]
    print("  Newton residual", mp.nstr(max(abs(v) for v in Fm), 5))
    zt = [A(v) for v in z]
    F0, J0 = FJ(zt)
    Ym = mp.inverse(mp.matrix([[amid(e) for e in row] for row in J0]))
    Y = arb_mat([[A(Ym[r, c]) for c in range(nv)] for r in range(nv)])
    rad = arb(10) ** (-(int(prec * 0.30) // 2))
    Z = [arb(zt[q].mid(), rad) for q in range(nv)]
    FZ, JZ = FJ(Z)
    K = arb_mat([[zt[q]] for q in range(nv)]) - Y * arb_mat([[f] for f in F0]) + \
        (arb_mat([[arb(1) if r == c else arb(0) for c in range(nv)] for r in range(nv)]) - Y * arb_mat(JZ)) * \
        arb_mat([[Z[q] - zt[q]] for q in range(nv)])
    ok = all((K[q, 0].mid() - K[q, 0].rad() > Z[q].mid() - Z[q].rad()) and
             (K[q, 0].mid() + K[q, 0].rad() < Z[q].mid() + Z[q].rad()) for q in range(nv))
    print("  Krawczyk (reduced symmetric system):", ok)
    if not ok:
        return
    P = [coords(Z, i) for i in range(n)]
    t = Z[it]
    print("  d* in", t.sqrt().str(40))
    # inactive strict
    for i in range(n):
        for j in range(i + 1, n):
            if (i, j) in Cset:
                continue
            s = (P[i][0] - P[j][0]) * (P[i][0] - P[j][0]) + (P[i][1] - P[j][1]) * (P[i][1] - P[j][1]) - t
            if not (s > 0):
                print("  inactive FAIL", i, j); ok = False
    for i in range(n):
        if i not in B:
            if not (1 - P[i][0] * P[i][0] - P[i][1] * P[i][1] > 0):
                print("  inactive bnd FAIL", i); ok = False
    print("  inactive constraints strict:", ok)
    # symmetric multipliers: unknowns lam_c (per contact orbit), mu_b (per boundary orbit)
    ncl, nbl = len(corb), len(borb)
    cidx = {}
    for q, ((i, j), m) in enumerate(corb):
        cidx[(i, j)] = q; cidx[norm_c((sig[i], sig[j]))] = q
    bidx = {}
    for q, (i, m) in enumerate(borb):
        bidx[i] = q; bidx[sig[i]] = q
    rows = []; rhs = []
    for i in reps:
        comps = (1,) if sig[i] == i else (0, 1)
        for comp in comps:
            row = [arb(0)] * (ncl + nbl)
            for (a, b) in C:
                if a == i:
                    row[cidx[(a, b)]] += P[i][comp] - P[b][comp]
                elif b == i:
                    row[cidx[(a, b)]] += P[i][comp] - P[a][comp]
            if i in B:
                row[ncl + bidx[i]] += -P[i][comp]
            rows.append(row); rhs.append(arb(0))
    rows.append([arb(m) for (c, m) in corb] + [arb(0)] * nbl); rhs.append(arb(1))
    print(f"  multiplier system: {len(rows)} equations, {ncl + nbl} unknowns")
    M = arb_mat(rows)
    if len(rows) != ncl + nbl:
        # least-squares not available rigorously; require square
        print("  multiplier system not square -> abort"); return
    sol = M.solve(arb_mat([[r] for r in rhs]))
    lamc = [sol[q, 0] for q in range(ncl)]; muc = [sol[ncl + q, 0] for q in range(nbl)]
    # verify the FULL equilibrium residual contains 0 (sanity, includes dropped/symmetric equations)
    lam = {c: lamc[cidx[c]] for c in C}
    mu = {i: muc[bidx[i]] for i in B}
    maxres = 0.0
    for i in range(n):
        for comp in (0, 1):
            r = arb(0)
            for (a, b) in C:
                if a == i:
                    r += lam[(a, b)] * (P[i][comp] - P[b][comp])
                elif b == i:
                    r += lam[(a, b)] * (P[i][comp] - P[a][comp])
            if i in B:
                r -= mu[i] * P[i][comp]
            if not r.contains(0):
                print("  equilibrium residual does not contain 0 at", i, comp, r); ok = False
    pos = all(l > 0 for l in lam.values()) and all(u > 0 for u in mu.values())
    print("  symmetric multipliers strictly positive:", pos, " min lambda >", min(float(l.mid() - l.rad()) for l in lam.values()),
          " min mu >", min(float(u.mid() - u.rad()) for u in mu.values()))
    ok = ok and pos
    # sigma from the FULL L (|C|+|B| rows, 2n columns)
    n2 = 2 * n
    Lr = []
    for (i, j) in C:
        r = [arb(0)] * n2
        for comp in (0, 1):
            r[2 * i + comp] = 2 * (P[i][comp] - P[j][comp]); r[2 * j + comp] = -2 * (P[i][comp] - P[j][comp])
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
    nrm = sum((v * v for v in Jx), arb(0)).sqrt(); u = [v / nrm for v in Jx]
    G = Lm.transpose() * Lm + arb_mat([[u[a] * u[b] for b in range(n2)] for a in range(n2)])
    Gf = np.array([[float(G[a, b].mid()) for b in range(n2)] for a in range(n2)])
    ev = np.linalg.eigvalsh(Gf)
    tau = arb(float(ev[0]) * 0.98)
    Ach = [[G[a, b] - (tau if a == b else 0) for b in range(n2)] for a in range(n2)]
    Lc = [[arb(0)] * n2 for _ in range(n2)]; pd = True
    for a in range(n2):
        s = Ach[a][a] - sum((Lc[a][q] * Lc[a][q] for q in range(a)), arb(0))
        if not (s > 0):
            pd = False; break
        Lc[a][a] = s.sqrt()
        for b in range(a + 1, n2):
            Lc[b][a] = (Ach[b][a] - sum((Lc[b][q] * Lc[a][q] for q in range(a)), arb(0))) / Lc[a][a]
    sigma = tau.sqrt()
    print("  PD:", pd, " sigma >=", sigma.str(8))
    ok = ok and pd
    K2 = arb(0)
    for l in lam.values():
        lo = arb(l.mid() - l.rad()); f = arb(1) if lo >= 1 else 1 / lo; K2 += 4 * f * f
    for u_ in mu.values():
        lo = arb(u_.mid() - u_.rad()); K2 += (2 / lo + 1) * (2 / lo + 1)
    dloc = sigma / K2.sqrt()
    print("  delta_loc >=", dloc.mid() - dloc.rad(), "  ALL OK:", ok)
    out = dict(n=n, ok=bool(ok), d_star=t.sqrt().str(45, radius=False), t_star_ball=t.str(50),
               delta_loc="[" + repr(math.nextafter(math.nextafter(float((dloc.mid() - dloc.rad()).mid()), -math.inf), -math.inf)) + " +/- 0]",
               points_mid=[[P[i][0].mid().str(45, radius=False), P[i][1].mid().str(45, radius=False)] for i in range(n)],
               boundary=B, contacts=C, symmetric=True)
    json.dump(out, open(os.path.join(ROOT, "known_packings", f"local_certificate_n{n}.json"), "w"), indent=1)


if __name__ == "__main__":
    main(int(sys.argv[1]))
