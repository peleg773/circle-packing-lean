"""Soundness test of the B&B pruning rules against KNOWN FEASIBLE configurations.

For every configuration found by the multistart searches (out/ms_n*_*.json; all local optima, all n):
  * unit-circle normalisation at its own rho_conf = 2/d, push-out at rho = rho_conf*(1+1e-12),
  * canonical interior form (s decreasing, psi_0 = 0, psi_1 in [0,pi]),
  * evaluate the rigorous box test (ringbb_rig.box_ok_rig) and the float test (ringbb2.box_ok) on
    (a) the degenerate point box and (b) a small random box containing the point.
A non-zero return (prune) on a feasible configuration would be a SOUNDNESS BUG.
Also checks that the configuration really is feasible (min distance >= 2 - 1e-9 after push-out).
"""
import json, glob, math, os, sys
import numpy as np
import ringbb_rig as RG
import ringbb2 as F

HERE = os.path.dirname(os.path.abspath(__file__))


def canonical_interior(C, rho):
    RI = math.sqrt(rho * rho - 4)
    r = np.hypot(C[:, 0], C[:, 1])
    Q = C.copy()
    out = r > RI
    Q[out] = Q[out] / r[out, None] * rho      # push-out
    # feasibility check
    D = np.sqrt(((Q[:, None] - Q[None]) ** 2).sum(-1)); np.fill_diagonal(D, 9)
    feas = D.min()
    I = Q[~out]
    s = np.hypot(I[:, 0], I[:, 1]); psi = np.arctan2(I[:, 1], I[:, 0])
    order = np.argsort(-s)
    s = s[order]; psi = psi[order]
    if len(s) == 0:
        return s, psi, int(out.sum()), feas
    psi = (psi - psi[0]) % (2 * math.pi)
    psi[0] = 0.0
    if len(s) >= 2 and psi[1] > math.pi:
        psi = (-psi) % (2 * math.pi)
        psi[0] = 0.0
    return s, psi, int(out.sum()), feas


def main():
    files = sorted(glob.glob(os.path.join(HERE, "out", "ms_n*_*.json")))
    rng = np.random.default_rng(0)
    ntest = 0; bad = 0; skipped = 0
    for fn in files:
        data = json.load(open(fn)); n = data["n"]
        for cl in data["clusters"]:
            P = np.array(cl["example"]["P"])
            Dm = np.sqrt(((P[:, None] - P[None]) ** 2).sum(-1)); np.fill_diagonal(Dm, 9)
            d = Dm.min()
            # make the test configuration STRICTLY feasible: min distance 2(1+1e-6)
            C = P * (2.0 * (1 + 1e-6) / d)
            rho = np.hypot(C[:, 0], C[:, 1]).max() * (1 + 1e-12)
            s, psi, nb, feas = canonical_interior(C, rho)
            k = len(s)
            if k < 2 or k > 13 or feas < 2 - 1e-9:
                skipped += 1
                continue
            params = RG.rigorous_params(n, rho)
            dl, dh, rih, rm = params
            delta = 2 * math.asin(1 / rho); RI = math.sqrt(rho * rho - 4)
            for trial in range(3):
                if trial == 0:
                    slo = s.copy(); shi = s.copy(); plo = psi.copy(); phi = psi.copy()
                else:
                    w = 10 ** rng.uniform(-6, -2)
                    slo = s - rng.uniform(0, w, k); shi = s + rng.uniform(0, w, k)
                    plo = psi - rng.uniform(0, w, k); phi = psi + rng.uniform(0, w, k)
                    plo[0] = 0.0; phi[0] = 0.0
                    slo = np.maximum(slo, 0.0)
                    if k >= 2:
                        plo[1] = max(plo[1], 0.0); phi[1] = min(phi[1], math.pi)
                    # keep ordering-consistent boxes: allow overlap only
                r1 = RG.box_ok_rig(slo.copy(), shi.copy(), plo.copy(), phi.copy(), k, n, rho, dl, dh, rih, rm)
                r2 = F.box_ok(slo.copy(), shi.copy(), plo.copy(), phi.copy(), k, n, rho, delta, RI, F.RHO_M, False)
                ntest += 1
                if r1 != 0 or r2 != 0:
                    bad += 1
                    print(f"PRUNED FEASIBLE: file={os.path.basename(fn)} n={n} d={d:.10f} k={k} B={nb} trial={trial} rig={r1} float={r2}")
    print(f"tests={ntest} bad={bad} skipped={skipped}")


if __name__ == "__main__":
    main()
