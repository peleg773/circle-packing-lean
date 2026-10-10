"""Reconstruct and analyse the best-known packings (Packomania) for n = 13..20.

For each n:
  * convert to point-separation normalisation (unit disk),
  * list boundary points and contacts (active constraints) with tolerance,
  * show the 'gap spectrum' (smallest inactive slacks) to detect near-contacts,
  * polish the configuration with high-precision Newton (Gauss-Newton) on the active set,
  * save JSON with coordinates (40 digits), boundary set, contact list, degrees.
Deterministic; no randomness.
"""
import json, os, sys
import mpmath as mp
from pk_common import *

mp.mp.dps = 60
OUT = os.path.join(ROOT, "known_packings")


def polish(pts, d, bnd, con, iters=60):
    """Gauss-Newton on equations |p_i|^2=1 (i in bnd), |p_i-p_j|^2=t (contacts), t=d^2 unknown.
    Gauge: none fixed explicitly; use least-norm steps (pseudo-inverse via QR of J J^T)."""
    n = len(pts)
    X = []
    for p in pts:
        X += [p[0], p[1]]
    t = d * d
    X.append(t)
    m = len(bnd) + len(con)
    N = 2 * n + 1
    for it in range(iters):
        F = mp.matrix(m, 1)
        J = mp.matrix(m, N)
        k = 0
        for i in bnd:
            x, y = X[2 * i], X[2 * i + 1]
            F[k] = x * x + y * y - 1
            J[k, 2 * i] = 2 * x
            J[k, 2 * i + 1] = 2 * y
            k += 1
        for (i, j) in con:
            dx, dy = X[2 * i] - X[2 * j], X[2 * i + 1] - X[2 * j + 1]
            F[k] = dx * dx + dy * dy - X[-1]
            J[k, 2 * i] = 2 * dx
            J[k, 2 * i + 1] = 2 * dy
            J[k, 2 * j] = -2 * dx
            J[k, 2 * j + 1] = -2 * dy
            J[k, N - 1] = -1
            k += 1
        res = max(abs(F[k]) for k in range(m))
        if res < mp.mpf(10) ** (-(mp.mp.dps - 8)):
            break
        # least-norm Gauss-Newton step: dX = -J^T (J J^T)^+ F ; use lstsq on J^T
        JJt = J * J.T
        # regularise tiny
        try:
            lam = mp.lu_solve(JJt + mp.eye(m) * mp.mpf(10) ** (-(mp.mp.dps - 5)), F)
        except ZeroDivisionError:
            break
        dX = J.T * lam
        for q in range(N):
            X[q] -= dX[q]
    newpts = [(X[2 * i], X[2 * i + 1]) for i in range(n)]
    return newpts, mp.sqrt(X[-1]), res


def rank_info(pts, bnd, con):
    """Rank of the rigidity-type Jacobian (numerical, float)."""
    import numpy as np
    n = len(pts)
    P = np.array([[float(p[0]), float(p[1])] for p in pts])
    rows = []
    for i in bnd:
        r = np.zeros(2 * n + 1); r[2 * i:2 * i + 2] = 2 * P[i]; rows.append(r)
    for (i, j) in con:
        r = np.zeros(2 * n + 1); dd = P[i] - P[j]
        r[2 * i:2 * i + 2] = 2 * dd; r[2 * j:2 * j + 2] = -2 * dd; r[-1] = -1; rows.append(r)
    J = np.array(rows)
    s = np.linalg.svd(J, compute_uv=False)
    return J.shape, s


def main(ns):
    summary = {}
    for n in ns:
        pts, d = load_cci(n, dps=60)
        ms = min_sep(pts)
        tol = mp.mpf("1e-20")
        bnd, con = active_sets(pts, d, tol)
        # gap spectrum
        dists = sorted(((dist(pts[i], pts[j]) - d, i, j) for i in range(n) for j in range(i + 1, n)), key=lambda z: z[0])
        inactive = [z for z in dists if z[0] >= tol][:6]
        bslack = sorted(((1 - norm(pts[i]), i) for i in range(n)), key=lambda z: z[0])
        binact = [z for z in bslack if z[0] >= tol][:4]
        newpts, dnew, res = polish(pts, d, bnd, con)
        shape, sv = rank_info(newpts, bnd, con)
        deg = [0] * n
        for (i, j) in con:
            deg[i] += 1; deg[j] += 1
        R = 1 + 2 / dnew
        print(f"=== n={n}: d(pack)={mp.nstr(d, 30)}  minsep={mp.nstr(ms, 30)}")
        print(f"   polished d={mp.nstr(dnew, 40)} residual={mp.nstr(res, 3)}  R=1+2/d={mp.nstr(R, 30)}")
        print(f"   boundary ({len(bnd)}): {bnd}")
        print(f"   contacts ({len(con)}): {con}")
        print(f"   degrees: {deg}  (deg 0 = rattler candidates: {[i for i in range(n) if deg[i]==0]})")
        print(f"   smallest inactive distance slacks: {[(mp.nstr(z[0], 5), z[1], z[2]) for z in inactive]}")
        print(f"   smallest inactive boundary slacks: {[(mp.nstr(z[0], 5), z[1]) for z in binact]}")
        print(f"   Jacobian {shape}, singular values (smallest 6): {sv[-6:]}")
        summary[n] = dict(
            n=n,
            d=mp.nstr(dnew, 40),
            R_unit_circles=mp.nstr(R, 40),
            points=[[mp.nstr(p[0], 40), mp.nstr(p[1], 40)] for p in newpts],
            boundary=bnd,
            contacts=con,
            degrees=deg,
            residual=mp.nstr(res, 5),
            source="Packomania cci%d.txt (E. Specht), converted p=c/(1-r), polished by Gauss-Newton on active set" % n,
        )
    with open(os.path.join(OUT, "known_packings_13_20.json"), "w") as f:
        json.dump(summary, f, indent=1)


if __name__ == "__main__":
    ns = [int(a) for a in sys.argv[1:]] or list(range(13, 21))
    main(ns)
