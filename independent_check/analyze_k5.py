"""Analyse the unresolved (surviving) boxes of a k=5 run: maximal distance of any point of
any surviving box from the matching vertex of the regular pentagon of circumradius
1/sin(36 deg) with a vertex at angle 0 (the canonical frame of bnb2)."""
import sys, json, math
import numpy as np
from core import maxdist2

res = json.load(open(sys.argv[1]))
S = np.array(res["survivor_boxes"])
r5 = 1.0 / math.sin(math.pi / 5)
print("rho", res["rho"], "k", res["k"], "tol", res["tol"], "nodes", res["nodes"],
      "done_volume", res.get("done_volume", "-"), "survivors", res["survivors"], "stored", len(S),
      "arithmetic", res.get("arithmetic", "float64+margins"))
worst = 0.0
worst_box = None
for B in S:
    dmax = 0.0
    used = set()
    for i in range(5):
        best = None
        for j in range(5):
            ang = 2 * math.pi * j / 5
            for sh in (-2 * math.pi, 0.0, 2 * math.pi):
                d = math.sqrt(maxdist2(B[i, 0], B[i, 1], B[i, 2], B[i, 3], r5, r5,
                                       ang + sh, ang + sh))
                if best is None or d < best[0]:
                    best = (d, j)
        used.add(best[1])
        dmax = max(dmax, best[0])
    assert len(used) == 5, "two points matched to the same vertex"
    if dmax > worst:
        worst = dmax
        worst_box = B
print("max over surviving boxes of max distance point->vertex: %.3e" % worst)
if worst_box is not None:
    print(np.array2string(worst_box, precision=10))
# spread of survivors
lo = S[:, :, [0, 2]].min(0)
hi = S[:, :, [1, 3]].max(0)
print("hull of survivors (s range, psi range) per point:")
for i in range(5):
    print("  point %d: s in [%.12f, %.12f]  psi in [%.12f, %.12f]" % (i, lo[i, 0], hi[i, 0],
                                                                      lo[i, 1], hi[i, 1]))
print("pentagon: r5 = %.12f, angles = %s" % (r5, [round(2 * math.pi * j / 5, 12) for j in range(5)]))
