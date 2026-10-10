"""Generate rig_consts.json: float brackets (lo <= x <= hi) of pi, 2pi, pi/2, the arcsine series coefficients
a_i = (2i)! / (4^i (i!)^2 (2i+1)), i = 0..60, and 1/(2i)!, i = 0..20, computed with arb (300 bits)."""
from flint import arb, ctx
import math, json, sys
ctx.prec = 300


def bracket(x):
    m = float(x.mid()); lo = m; hi = m
    xl = x.mid() - x.rad(); xh = x.mid() + x.rad()
    while arb(lo) > xl:
        lo = math.nextafter(lo, -math.inf)
    while arb(hi) < xh:
        hi = math.nextafter(hi, math.inf)
    return math.nextafter(lo, -math.inf), math.nextafter(hi, math.inf)


pi = arb.pi()
consts = {"PI": bracket(pi), "TWO_PI": bracket(2 * pi), "HALF_PI": bracket(pi / 2)}
coef = [bracket(arb.fac_ui(2 * i) / (arb(4) ** i * arb.fac_ui(i) ** 2 * (2 * i + 1))) for i in range(61)]
ccoef = [bracket(1 / arb.fac_ui(2 * i)) for i in range(21)]
out = sys.argv[1] if len(sys.argv) > 1 else "rig_consts.json"
json.dump(dict(consts=consts, asin=coef, cos=ccoef), open(out, "w"))
print("written", out)
