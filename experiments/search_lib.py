"""Numerical search tools (floating point; NOT rigorous).

Problem: n points in the closed unit disk, maximise d = min |p_i - p_j|.

* penalty_energy: E(P; d) = sum_{i<j} max(0, d^2-|pi-pj|^2)^2 + w * sum_i max(0,|pi|^2-1)^2
* polish_maxmin: SLSQP on (P, t): max t s.t. |pi|^2<=1, |pi-pj|^2>=t
* contact analysis + canonical graph signature
"""
import numpy as np
import numba as nb
from scipy.optimize import minimize


@nb.njit(cache=True)
def energy_grad(z, d2, wb):
    n = z.shape[0] // 2
    g = np.zeros_like(z)
    E = 0.0
    for i in range(n):
        xi = z[2 * i]; yi = z[2 * i + 1]
        r2 = xi * xi + yi * yi
        if r2 > 1.0:
            v = r2 - 1.0
            E += wb * v * v
            g[2 * i] += wb * 4.0 * v * xi
            g[2 * i + 1] += wb * 4.0 * v * yi
        for j in range(i + 1, n):
            dx = xi - z[2 * j]; dy = yi - z[2 * j + 1]
            s2 = dx * dx + dy * dy
            if s2 < d2:
                v = d2 - s2
                E += v * v
                gx = -4.0 * v * dx; gy = -4.0 * v * dy
                g[2 * i] += gx; g[2 * i + 1] += gy
                g[2 * j] -= gx; g[2 * j + 1] -= gy
    return E, g


def penalty_minimize(P0, d, wb=4.0, maxiter=3000, gtol=1e-14):
    z0 = P0.reshape(-1).astype(np.float64).copy()
    d2 = d * d
    res = minimize(lambda z: energy_grad(z, d2, wb), z0, jac=True, method="L-BFGS-B",
                   options=dict(maxiter=maxiter, gtol=gtol, ftol=1e-20, maxcor=30))
    return res.x.reshape(-1, 2), res.fun


def min_sep(P):
    D = np.sqrt(((P[:, None, :] - P[None, :, :]) ** 2).sum(-1))
    iu = np.triu_indices(len(P), 1)
    return D[iu].min()


def project_into_disk(P):
    r = np.sqrt((P ** 2).sum(1))
    Q = P.copy()
    m = r > 1
    Q[m] /= r[m][:, None]
    return Q


def polish_maxmin(P0, maxiter=500, ftol=1e-15):
    n = len(P0)
    iu, ju = np.triu_indices(n, 1)
    P0 = project_into_disk(P0)
    t0 = min_sep(P0) ** 2
    z0 = np.concatenate([P0.reshape(-1), [t0]])

    def f(z):
        return -z[-1]

    def fg(z):
        g = np.zeros_like(z); g[-1] = -1.0
        return g

    def cons(z):
        P = z[:-1].reshape(-1, 2)
        dd = P[iu] - P[ju]
        c1 = (dd ** 2).sum(1) - z[-1]
        c2 = 1.0 - (P ** 2).sum(1)
        return np.concatenate([c1, c2])

    def cons_jac(z):
        P = z[:-1].reshape(-1, 2)
        m1 = len(iu)
        J = np.zeros((m1 + n, 2 * n + 1))
        dd = P[iu] - P[ju]
        rows = np.arange(m1)
        J[rows, 2 * iu] = 2 * dd[:, 0]
        J[rows, 2 * iu + 1] = 2 * dd[:, 1]
        J[rows, 2 * ju] = -2 * dd[:, 0]
        J[rows, 2 * ju + 1] = -2 * dd[:, 1]
        J[rows, -1] = -1.0
        r2 = np.arange(n)
        J[m1 + r2, 2 * r2] = -2 * P[:, 0]
        J[m1 + r2, 2 * r2 + 1] = -2 * P[:, 1]
        return J

    res = minimize(f, z0, jac=fg, method="SLSQP",
                   constraints=[dict(type="ineq", fun=cons, jac=cons_jac)],
                   options=dict(maxiter=maxiter, ftol=ftol))
    P = project_into_disk(res.x[:-1].reshape(-1, 2))
    return P, min_sep(P)


def contact_structure(P, d=None, tol=1e-7):
    n = len(P)
    if d is None:
        d = min_sep(P)
    r = np.sqrt((P ** 2).sum(1))
    bnd = [i for i in range(n) if r[i] > 1 - tol]
    D = np.sqrt(((P[:, None, :] - P[None, :, :]) ** 2).sum(-1))
    con = [(i, j) for i in range(n) for j in range(i + 1, n) if D[i, j] < d * (1 + tol)]
    return bnd, con


def graph_signature(n, bnd, con):
    """Isomorphism-invariant signature of the contact graph with boundary marking (WL hash)."""
    import networkx as nx
    G = nx.Graph()
    for i in range(n):
        G.add_node(i, b=("B" if i in bnd else "I"))
    G.add_edges_from(con)
    return nx.weisfeiler_lehman_graph_hash(G, node_attr="b", iterations=5)


def random_disk(n, rng):
    r = np.sqrt(rng.random(n))
    th = rng.random(n) * 2 * np.pi
    return np.stack([r * np.cos(th), r * np.sin(th)], 1)
