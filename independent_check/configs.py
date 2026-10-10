"""
Explicit configurations (for validation of the B&B, not part of the proof).

Model ("reduced" model of F1/F3): k interior centres with |P_i| <= R_I(rho)=sqrt(rho^2-4),
m = 15-k boundary centres rho*e^{i a_j}; all 15 centres pairwise >= 2 apart.
"""
import math
import numpy as np
from scipy.optimize import minimize


def unpack(x, k, m):
    rho = x[0]
    P = x[1:1 + 2 * k].reshape(k, 2)
    a = x[1 + 2 * k:1 + 2 * k + m]
    return rho, P, a


def all_points(rho, P, a):
    Q = np.stack([rho * np.cos(a), rho * np.sin(a)], axis=1)
    return np.vstack([P, Q])


def cons_fun(x, k, m):
    rho, P, a = unpack(x, k, m)
    X = all_points(rho, P, a)
    n = k + m
    iu = np.triu_indices(n, 1)
    d2 = ((X[:, None, :] - X[None, :, :]) ** 2).sum(-1)[iu] - 4.0
    rad = (rho * rho - 4.0) - (P ** 2).sum(1)
    return np.concatenate([d2, rad])


def min_rho(k, seed, rho0=3.9, iters=400):
    """SLSQP: minimise rho over the reduced model with k interior points."""
    m = 15 - k
    rng = np.random.default_rng(seed)
    r = 2.9 * np.sqrt(rng.uniform(0, 1, k))
    t = rng.uniform(0, 2 * np.pi, k)
    P = np.stack([r * np.cos(t), r * np.sin(t)], 1)
    a = np.sort(rng.uniform(0, 2 * np.pi, m))
    x0 = np.concatenate([[rho0], P.ravel(), a])
    res = minimize(lambda x: x[0], x0, jac=lambda x: np.eye(len(x))[0],
                   constraints=[{'type': 'ineq', 'fun': cons_fun, 'args': (k, m)}],
                   bounds=[(3.0, 5.0)] + [(-3.0, 3.0)] * (2 * k) + [(-7.0, 14.0)] * m,
                   method='SLSQP', options={'maxiter': iters, 'ftol': 1e-13})
    x = res.x
    viol = -min(0.0, cons_fun(x, k, m).min())
    return x, viol


def feasible_at(x, k, rho_new):
    """A configuration feasible at rho stays feasible at rho_new >= rho if the boundary
    centres keep their angles (F2 monotonicity).  Returns (P, a)."""
    rho, P, a = unpack(x, k, 15 - k)
    assert rho_new >= rho
    return P.copy(), a.copy()


def check_config(P, a, rho, tol=0.0):
    """exact-ish float check of the reduced model; returns min slack."""
    X = all_points(rho, P, a)
    n = len(X)
    d = np.sqrt(((X[:, None, :] - X[None, :, :]) ** 2).sum(-1))
    d[np.arange(n), np.arange(n)] = 99
    s1 = d.min() - 2.0
    s2 = math.sqrt(rho * rho - 4) - np.sqrt((P ** 2).sum(1)).max()
    return min(s1, s2)


def random_feasible(k, rho, seed, tries=50):
    """Random feasible configuration at fixed rho by penalty minimisation from random
    starts (only works when rho is comfortably above the critical value)."""
    m = 15 - k
    rng = np.random.default_rng(seed)
    RI = math.sqrt(rho * rho - 4)
    for t in range(tries):
        r = RI * np.sqrt(rng.uniform(0, 1, k))
        th = rng.uniform(0, 2 * np.pi, k)
        P = np.stack([r * np.cos(th), r * np.sin(th)], 1)
        a = np.sort(rng.uniform(0, 2 * np.pi, m))
        y0 = np.concatenate([P.ravel(), a])

        def pen(y):
            x = np.concatenate([[rho], y])
            c = cons_fun(x, k, m)
            # add a small margin so the result is strictly feasible
            c = c - 1e-6
            v = np.minimum(c, 0.0)
            return (v * v).sum()
        res = minimize(pen, y0, method='L-BFGS-B', options={'maxiter': 3000})
        y = res.x
        P = y[:2 * k].reshape(k, 2)
        a = y[2 * k:]
        if check_config(P, a, rho) >= 0.0:
            return P, a
    return None


def canonical(P):
    """Canonical labelling used by bnb2: point 0 of maximal radius at angle 0, others by
    increasing angle in [0,2pi), reflection so that psi_1 + psi_{k-1} <= 2pi.
    Returns array (k, 2) of (s, psi)."""
    k = len(P)
    s = np.sqrt((P ** 2).sum(1))
    i0 = int(np.argmax(s))
    ang = np.arctan2(P[:, 1], P[:, 0]) - math.atan2(P[i0, 1], P[i0, 0])
    ang = np.mod(ang, 2 * np.pi)
    ang[i0] = 0.0
    others = [i for i in range(k) if i != i0]
    out = []
    for refl in (False, True):
        a2 = ang.copy()
        if refl:
            a2 = np.mod(-a2, 2 * np.pi)
            a2[i0] = 0.0
        order = sorted(others, key=lambda i: a2[i])
        C = np.array([[s[i0], 0.0]] + [[s[i], a2[i]] for i in order])
        out.append(C)
    C = out[0]
    if k >= 3 and C[1, 1] + C[k - 1, 1] > 2 * np.pi:
        C = out[1]
    return C
