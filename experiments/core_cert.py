"""Local-uniqueness certificate (lemma L7) for configurations with EXACT algebraic coordinates and possibly
overdetermined active sets (|B| + |C| > 2n), e.g. cores of the n = 18 optimal structures built on the
19-packing lattice:  centre 0, ring points 2 e^{i k pi/3}, boundary points rho19 e^{i (pi/12 + j pi/6)},
rho19 = 1/sin(pi/12) = sqrt6 + sqrt2.

Exactness of the active constraints is by construction (trigonometric identities:
  |2 - rho19 e^{i pi/12}|^2 = 4 + rho19^2 - 4 rho19 cos(pi/12) = 4  since cos(pi/12) = rho19/4;
  |rho19 e^{i a} - rho19 e^{i(a+pi/6)}| = 2 rho19 sin(pi/12) = 2;  ring-ring and centre-ring distances = 2);
arb is used to (i) confirm consistency of the active set (balls contain the exact values) and strictness of all
inactive constraints, (ii) compute an exact positive multiplier vector, (iii) certify sigma and delta_loc.

Multipliers: a strictly positive candidate is found by LP (float); then all multipliers outside a selected
nonsingular square subsystem are fixed to rational values and the subsystem is solved in arb; every multiplier
must be certified > 0.
Usage: python core_cert.py <structure-name>
"""
import sys, os, json, math
import numpy as np
from scipy.optimize import linprog
from flint import arb, arb_mat, ctx

ctx.prec = 256
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(HERE)
PI = arb.pi()
RHO19 = 1 / (PI / 12).sin()


def lattice_point(kind, idx):
    if kind == "centre":
        return (arb(0), arb(0))
    if kind == "ring":
        a = PI * idx / 3
        return (2 * a.cos(), 2 * a.sin())
    if kind == "outer":
        a = PI / 12 + PI * idx / 6
        return (RHO19 * a.cos(), RHO19 * a.sin())
    raise ValueError(kind)


STRUCTURES = {
    # 19-packing minus the two outer points of the window between ring directions 300 and 360 degrees
    "n18_hexagon_core17": [("centre", 0)] + [("ring", k) for k in range(6)] + [("outer", j) for j in range(10)],
    # full 19-packing (calibration of this script: proven optimal by Fodor 1999)
    "n19_full": [("centre", 0)] + [("ring", k) for k in range(6)] + [("outer", j) for j in range(12)],
}


def certify(name):
    if name.startswith("n18:"):
        from n18_structures import build
        pts, interior, boundary, core = build(name[4:])
        C = [pts[i] for i in core]
        spec = [str(i) for i in core]
    else:
        spec = STRUCTURES[name]
        C = [lattice_point(*s) for s in spec]
    n = len(C)
    rho = RHO19
    P = [(x / rho, y / rho) for x, y in C]           # point normalisation
    t = (2 / rho) * (2 / rho)                         # t* = d*^2
    # active sets (consistency check in arb)
    Bset = []; Cset = []
    for i in range(n):
        r2 = P[i][0] * P[i][0] + P[i][1] * P[i][1]
        if r2.overlaps(arb(1)):
            Bset.append(i)
        elif not (r2 < 1):
            raise RuntimeError(f"point {i} outside the disk")
    for i in range(n):
        for j in range(i + 1, n):
            dx = P[i][0] - P[j][0]; dy = P[i][1] - P[j][1]
            v = dx * dx + dy * dy
            if v.overlaps(t):
                Cset.append((i, j))
            elif not (v > t):
                raise RuntimeError(f"pair {i},{j} too close")
    print(f"{name}: n={n}  boundary={len(Bset)}  contacts={len(Cset)}  (2n={2*n})")
    m1, m2 = len(Cset), len(Bset)
    m = m1 + m2
    # equilibrium matrix (2n x m) in float for the LP and subsystem choice
    Pf = np.array([[float(x.mid()), float(y.mid())] for x, y in P])
    Aeq = np.zeros((2 * n, m))
    for k, (a, b) in enumerate(Cset):
        Aeq[2 * a:2 * a + 2, k] += Pf[a] - Pf[b]
        Aeq[2 * b:2 * b + 2, k] += Pf[b] - Pf[a]
    for q, i in enumerate(Bset):
        Aeq[2 * i:2 * i + 2, m1 + q] = -Pf[i]
    A2 = np.vstack([np.c_[Aeq, np.zeros(2 * n)], np.r_[np.ones(m1), np.zeros(m2), 0]])
    res = linprog(np.r_[np.zeros(m), -1], A_ub=np.c_[-np.eye(m), np.ones(m)], b_ub=np.zeros(m),
                  A_eq=A2, b_eq=np.r_[np.zeros(2 * n), 1], bounds=[(0, None)] * m + [(None, None)], method="highs")
    if res.status != 0 or -res.fun <= 1e-9:
        print("  no strictly positive multiplier vector (LP max-min =", -res.fun if res.status == 0 else res.message, ")")
        return None
    lam0 = res.x[:m]
    print(f"  LP max-min multiplier: {-res.fun:.6f}")
    # choose a square nonsingular subsystem: rows = all 2n equilibrium eqs except one (torque redundancy) + normalisation;
    # columns S chosen by pivoted QR on the float matrix
    import scipy.linalg as sla
    rows_all = np.vstack([Aeq, np.r_[np.ones(m1), np.zeros(m2)]])
    # drop one equilibrium row: the x-equation at the point with largest |y|
    mrow = int(np.argmax(np.abs(Pf[:, 1])))
    keep = [r for r in range(2 * n) if r != 2 * mrow] + [2 * n]
    Mf = rows_all[keep]
    q, r, piv = sla.qr(Mf, pivoting=True)
    S = sorted(piv[:Mf.shape[0]])
    F = [c for c in range(m) if c not in S]
    # exact arb system
    def colvec(c):
        v = [arb(0)] * (2 * n)
        if c < m1:
            a, b = Cset[c]
            for comp in (0, 1):
                v[2 * a + comp] += P[a][comp] - P[b][comp]
                v[2 * b + comp] += P[b][comp] - P[a][comp]
        else:
            i = Bset[c - m1]
            for comp in (0, 1):
                v[2 * i + comp] = -P[i][comp]
        norm = arb(1) if c < m1 else arb(0)
        return v + [norm]
    cols = {c: colvec(c) for c in range(m)}
    fixed = {c: arb(float(lam0[c])) for c in F}     # exact binary rationals (floats are exact in arb)
    rhs = [arb(0)] * (2 * n) + [arb(1)]
    for c in F:
        for r_ in range(2 * n + 1):
            rhs[r_] -= fixed[c] * cols[c][r_]
    Mrows = [[cols[c][r_] for c in S] for r_ in keep]
    sol = arb_mat(Mrows).solve(arb_mat([[rhs[r_]] for r_ in keep]))
    lam = dict(fixed)
    for idx, c in enumerate(S):
        lam[c] = sol[idx, 0]
    # verify the dropped equation (torque identity) and positivity
    pos = all(lam[c] > 0 for c in range(m))
    yv = P[mrow][1]
    print(f"  multipliers certified positive: {pos};  min lower bound = {min(float(lam[c].mid() - lam[c].rad()) for c in range(m)):.6f};  dropped-eq point y = {float(yv.mid()):.4f} (nonzero: {not yv.contains(0)})")
    # sigma via Cholesky of L^T L + u u^T
    n2 = 2 * n
    Lr = []
    for (i, j) in Cset:
        rw = [arb(0)] * n2
        for comp in (0, 1):
            rw[2 * i + comp] = 2 * (P[i][comp] - P[j][comp]); rw[2 * j + comp] = -2 * (P[i][comp] - P[j][comp])
        Lr.append(rw)
    for i in Bset:
        rw = [arb(0)] * n2
        for comp in (0, 1):
            rw[2 * i + comp] = -2 * P[i][comp]
        Lr.append(rw)
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
        s = Ach[a][a] - sum((Lc[a][qq] * Lc[a][qq] for qq in range(a)), arb(0))
        if not (s > 0):
            pd = False; break
        Lc[a][a] = s.sqrt()
        for b in range(a + 1, n2):
            Lc[b][a] = (Ach[b][a] - sum((Lc[b][qq] * Lc[a][qq] for qq in range(a)), arb(0))) / Lc[a][a]
    sigma = tau.sqrt()
    print(f"  sigma >= {float(sigma.mid()):.6f} (PD certified: {pd});  float eigs: {ev[0]:.4g}, {ev[1]:.4g}")
    K2 = arb(0)
    for c in range(m):
        lo = arb(lam[c].mid() - lam[c].rad())
        if c < m1:
            f = arb(1) if lo >= 1 else 1 / lo
            K2 += 4 * f * f
        else:
            K2 += (2 / lo + 1) * (2 / lo + 1)
    dloc = sigma / K2.sqrt()
    dl = float((dloc.mid() - dloc.rad()).mid())
    ok = pos and pd and not yv.contains(0)
    print(f"  delta_loc >= {dl:.4e}   ALL OK: {ok}")
    out = dict(name=name, n=n, ok=bool(ok), d_star="2 sin(pi/12)", delta_loc=dl, boundary=Bset, contacts=Cset,
               structure=spec)
    json.dump(out, open(os.path.join(ROOT, "known_packings", f"core_certificate_{name.replace(chr(58), chr(95))}.json"), "w"), indent=1)
    return out


if __name__ == "__main__":
    certify(sys.argv[1])
