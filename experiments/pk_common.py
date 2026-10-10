"""Common utilities for the circle-in-circle packing project.

Normalizations
--------------
* Packomania (cci): container radius 1, equal circles of radius r, centres c_i with |c_i| <= 1 - r.
* Point-separation (this project): points p_i in closed unit disk, d = min |p_i - p_j|.
    p_i = c_i / (1 - r),   d = 2 r / (1 - r).
* Unit-circle packing: unit circles in container of radius R = 1 + 2/d = 1/r.
"""
import os
import mpmath as mp

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
RAW = os.path.join(ROOT, "known_packings", "packomania_raw")

# Packomania "radius" column (container radius 1), 30 digits, from cci.html (last update 25-Dec-2024)
PACKOMANIA_R = {
    13: "0.236067977499789696409173668731",
    14: "0.231030727971008638446179972284",
    15: "0.221172539086390937264316484926",
    16: "0.216664742924422421010647936933",
    17: "0.208679665570499743200080125264",
    18: "0.205604646759568224693193969093",
    19: "0.205604646759568224693193969093",
    20: "0.195224011018748878291305694833",
}


def load_cci(n, dps=40):
    """Load Packomania coordinates for n; return (points in unit disk, d) as mpf at given precision."""
    mp.mp.dps = dps
    r = mp.mpf(PACKOMANIA_R[n])
    pts = []
    with open(os.path.join(RAW, f"cci{n}.txt")) as f:
        for line in f:
            s = line.split()
            if len(s) < 3:
                continue
            x, y = mp.mpf(s[1]), mp.mpf(s[2])
            pts.append((x / (1 - r), y / (1 - r)))
    assert len(pts) == n, (n, len(pts))
    d = 2 * r / (1 - r)
    return pts, d


def dist(p, q):
    return mp.sqrt((p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2)


def norm(p):
    return mp.sqrt(p[0] ** 2 + p[1] ** 2)


def min_sep(pts):
    n = len(pts)
    return min(dist(pts[i], pts[j]) for i in range(n) for j in range(i + 1, n))


def active_sets(pts, d, tol):
    n = len(pts)
    bnd = [i for i in range(n) if 1 - norm(pts[i]) < tol]
    con = [(i, j) for i in range(n) for j in range(i + 1, n) if dist(pts[i], pts[j]) - d < tol]
    return bnd, con


def R_from_d(d):
    return 1 + 2 / d


def d_from_R(R):
    return 2 / (R - 1)
