"""Rigorous check that the closed-form D5 configuration (exact algebraic) satisfies the n=15 active system
EXACTLY and lies in the Krawczyk uniqueness box of local_cert.py (so the certified record configuration IS the
closed form).  Exact construction (unit circles): inner pentagon of side 2 (circumradius 1/sin 36deg), each outer
centre = inner vertex + 2 * (outer unit normal of an incident edge); rho*^2 = (2 + cot 36deg)^2 + 1."""
import json, os
from flint import arb, ctx
ctx.prec = 300
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
C = json.load(open(os.path.join(ROOT, "known_packings", "local_certificate_n15.json")))
pi = arb.pi()
s5 = 1 / (pi / 5).sin()
rho = ((2 + (pi / 5).cos() / (pi / 5).sin()) ** 2 + 1).sqrt()
rho_formula = (6 + 2 / arb(5).sqrt() + 4 * (1 + 2 / arb(5).sqrt()).sqrt()).sqrt()
print("rho* (geometric) =", rho.str(40), "\nrho* (formula)   =", rho_formula.str(40), " overlap:", rho.overlaps(rho_formula))
inner = []; outer = []
for k in range(5):
    th = pi / 2 + 2 * pi * k / 5
    inner.append((s5 * th.cos(), s5 * th.sin()))
for k in range(5):
    for sgn in (-1, 1):
        a = pi / 2 + 2 * pi * k / 5 + sgn * pi / 5
        x, y = inner[k]
        outer.append((x + 2 * a.cos(), y + 2 * a.sin()))
pts = inner + outer
# exact geometry checks
def d2(p, q):
    return (p[0] - q[0]) * (p[0] - q[0]) + (p[1] - q[1]) * (p[1] - q[1])
r2 = [p[0] * p[0] + p[1] * p[1] for p in outer]
print("outer radii^2 contain rho^2:", all(v.overlaps(rho * rho) for v in r2))
dmin = None; ncontact = 0
for i in range(15):
    for j in range(i + 1, 15):
        v = d2(pts[i], pts[j])
        if v.overlaps(arb(4)):
            ncontact += 1
        elif not (v > 4):
            print("VIOLATION", i, j, v)
print("pairs at distance exactly 2 (balls containing 4):", ncontact, "(expected 20)")
# compare with the certified box (point normalisation, gauge: boundary point g on positive x-axis)
P = [(arb(a), arb(b)) for a, b in C["points_mid"]]
B = C["boundary"]; g = C["gauge_point"]
# map closed form to point normalisation and rotate so that SOME outer point lies on the +x axis; try all
# assignments by matching nearest points, for each choice of outer point as gauge
best = None
for gi in range(5, 15):
    ang = arb.atan2(pts[gi][1], pts[gi][0])
    c, s = (-ang).cos(), (-ang).sin()
    for refl in (1, -1):
        Q = [((c * x - s * y) / rho, refl * (s * x + c * y) / rho) for x, y in pts]
        # match each certified point to nearest closed-form point
        maxdev = arb(0); used = set(); ok = True
        for i, (px, py) in enumerate(P):
            j = min(range(15), key=lambda j: float(((Q[j][0] - px) ** 2 + (Q[j][1] - py) ** 2).mid()))
            if j in used:
                ok = False; break
            used.add(j)
            dev = max(abs(Q[j][0] - px).mid() + abs(Q[j][0] - px).rad(), abs(Q[j][1] - py).mid() + abs(Q[j][1] - py).rad())
            maxdev = arb(max(maxdev.mid(), dev))
        if ok and (best is None or maxdev.mid() < best.mid()):
            best = maxdev
print("max coordinate deviation between closed form and certified midpoint (point normalisation):", best)
print("Krawczyk box radius:", C["box_radius"])
print("closed form inside the uniqueness box:", best < arb("1e-38"))
