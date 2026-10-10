"""Start SLSQP (minimise rho in the reduced model) from the centre of an unresolved B&B box.
Used to decide whether survivors at a given rho come from genuinely feasible configurations."""
import sys, json, math
import numpy as np
from scipy.optimize import minimize
from configs import cons_fun, unpack, check_config

def greedy_boundary(P, rho, m):
    # boundary angles: avoid forbidden arcs of interior points, greedy from several starts
    db = 2*math.asin(1/rho)
    arcs = []
    for (x, y) in P:
        s = math.hypot(x, y); psi = math.atan2(y, x)
        c = (s*s + rho*rho - 4)/(2*s*rho) if s > 0 else 2
        if c < 1:
            th = math.acos(max(-1, c)); arcs.append((psi - th, psi + th))
    best = None
    for st in np.linspace(0, 2*math.pi, 720, endpoint=False):
        pts = []; x = st
        while x < st + 2*math.pi - db + 1e-12 and len(pts) < m:
            ok = all(not (0 < ((x - a) % (2*math.pi)) < (b - a)) for (a, b) in arcs)
            if ok: pts.append(x); x += db
            else: x += 0.002
        if best is None or len(pts) > len(best): best = pts
    while len(best) < m: best.append(best[-1] + db)
    return np.array(best[:m])

def polish(B, rho, k):
    m = 15 - k
    s = 0.5*(B[:, 0] + B[:, 1]); p = 0.5*(B[:, 2] + B[:, 3])
    P = np.stack([s*np.cos(p), s*np.sin(p)], 1)
    a = greedy_boundary(P, rho, m)
    x0 = np.concatenate([[rho], P.ravel(), a])
    res = minimize(lambda x: x[0], x0, jac=lambda x: np.eye(len(x))[0],
                   constraints=[{'type': 'ineq', 'fun': cons_fun, 'args': (k, m)}],
                   bounds=[(3.0, 5.0)] + [(-3.0, 3.0)]*(2*k) + [(-7.0, 14.0)]*m,
                   method='SLSQP', options={'maxiter': 1000, 'ftol': 1e-14})
    x = res.x
    r, P2, a2 = unpack(x, k, m)
    return r, check_config(P2, a2, r + 1e-9), x

if __name__ == "__main__":
    L = json.load(open("results/threshold_validation.json"))
    for r in L:
        if r["k"] == 10 and abs(r["rho"] - 3.70) < 1e-9:
            B = np.array(r["first_survivor"])
            print("first survivor box (k=10, rho=3.70):"); print(np.array2string(B, precision=4))
            rr, sl, x = polish(B, 3.70, 10)
            print("SLSQP from its centre: rho = %.10f, min slack at rho+1e-9 = %.2e" % (rr, sl))
            json.dump({"rho": rr, "x": x.tolist()}, open("results/k10_polished.json", "w"))
