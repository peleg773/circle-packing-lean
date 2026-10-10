"""Exact descriptions of n = 18 optimal structures at rho_19 = 1/sin(pi/12) (unit circles), in push-out form.
Each structure: list of points (kind, angle in units of pi/12, radius tag) with exact coordinates built in arb:
  radius tags: 'c' -> 0 (centre), 'r' -> 2 (ring), 's' -> 2 sqrt2, 'b' -> rho19 (boundary).
A structure lists its interior points and boundary points; 'core' lists indices forming a certified rigid core.
(All angles are multiples of 15 degrees for the structures found numerically; this file is extended as the
search reveals structures.)"""
from flint import arb

PI = arb.pi()
RHO19 = 1 / (PI / 12).sin()
RAD = {"c": arb(0), "r": arb(2), "s": 2 * arb(2).sqrt(), "b": RHO19}


def point(tag, a15):
    r = RAD[tag]
    a = PI * a15 / 12
    return (r * a.cos(), r * a.sin())


# 19-packing lattice: ring at 60 k deg (a15 = 4k), boundary at 15 + 30 j deg (a15 = 1 + 2j)
STRUCTURES = {
    # family (c): 19-packing minus the outer point at 345 deg (a15 = 23); core = minus also 315 deg (a15 = 21)
    "hexagon_B11": dict(
        points=[("c", 0)] + [("r", 4 * k) for k in range(6)] + [("b", 1 + 2 * j) for j in range(11)],
        core_drop=[("b", 21)]),
    # centre + 5 ring (missing 0 deg) + 2sqrt2-point at 15 deg + 11 boundary (all lattice slots except 15 deg)
    "five_ring_one_s_B11": dict(
        points=[("c", 0)] + [("r", 4 * k) for k in range(1, 6)] + [("s", 1)] + [("b", 1 + 2 * j) for j in range(1, 12)],
        core_drop=[]),
    # k = 8, B = 10: centre; ring at 0, +-60, +-150 deg; 2sqrt2-points at +-105 deg; boundary at
    # +-15, +-45, +-75, +-135, +-165 deg  (found numerically, multistart cluster 7)
    "k8_two_s_B10": dict(
        points=[("c", 0), ("r", 0), ("r", 4), ("r", 20), ("r", 10), ("r", 14), ("s", 7), ("s", 17)]
               + [("b", a) for a in (1, 23, 3, 21, 5, 19, 9, 15, 11, 13)],
        core_drop=[]),
}


def build(name):
    S = STRUCTURES[name]
    pts = [point(t, a) for t, a in S["points"]]
    tags = [t for t, a in S["points"]]
    interior = [i for i, t in enumerate(tags) if t != "b"]
    boundary = [i for i, t in enumerate(tags) if t == "b"]
    drop = set(S["points"].index(p) for p in S["core_drop"])
    core = [i for i in range(len(pts)) if i not in drop]
    return pts, interior, boundary, core
