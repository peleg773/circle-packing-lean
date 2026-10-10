"""Cluster n=18 survivor boxes (float, exploration) and compare with known structures.
Usage: python analyze_survivors_n18.py k survivors.npy"""
import sys, math
import numpy as np
from scipy.optimize import linear_sum_assignment
from n18_structures import STRUCTURES, build

k = int(sys.argv[1]); S = np.load(sys.argv[2])
cen = []
for bx in S:
    slo = bx[0:k]; shi = bx[k:2 * k]; plo = bx[2 * k:3 * k]; phi = bx[3 * k:4 * k]
    s = 0.5 * (slo + shi); p = 0.5 * (plo + phi)
    cen.append(np.stack([s * np.cos(p), s * np.sin(p)], 1))
cen = np.array(cen)
print(f"{len(S)} survivor boxes; max box widths: s {np.max(S[:, k:2*k] - S[:, 0:k]):.3g}, psi {np.max(S[:, 3*k:4*k] - S[:, 2*k:3*k]):.3g}")
# reference variants
refs = []
for nm in STRUCTURES:
    pts, interior, boundary, core = build(nm)
    if len(interior) != k:
        continue
    P = np.array([[float(p[0].mid()), float(p[1].mid())] for p in pts])[interior]
    r = np.hypot(P[:, 0], P[:, 1]); rmax = r.max()
    for t in np.where(np.abs(r - rmax) < 1e-9)[0]:
        a0 = math.atan2(P[t, 1], P[t, 0])
        R = np.array([[math.cos(-a0), -math.sin(-a0)], [math.sin(-a0), math.cos(-a0)]])
        Q = P @ R.T
        refs.append((nm, Q)); refs.append((nm, Q * np.array([1, -1])))
assigned = {}
unmatched = []
for t in range(len(cen)):
    best = (1e9, None)
    for nm, Q in refs:
        D = np.linalg.norm(cen[t][:, None, :] - Q[None, :, :], axis=2)
        r, c = linear_sum_assignment(D)
        m = D[r, c].max()
        if m < best[0]:
            best = (m, nm)
    if best[0] < 0.05:
        assigned[best[1]] = assigned.get(best[1], 0) + 1
    else:
        unmatched.append(t)
print("assigned to known structures:", assigned, " unmatched:", len(unmatched))
# cluster unmatched by rounded configuration signature (sorted radii)
sig = {}
for t in unmatched:
    rs = tuple(np.round(np.sort(np.hypot(cen[t][:, 0], cen[t][:, 1]))[::-1], 1))
    sig.setdefault(rs, []).append(t)
for rs, lst in sorted(sig.items(), key=lambda z: -len(z[1]))[:15]:
    t = lst[0]
    ang = np.degrees(np.arctan2(cen[t][:, 1], cen[t][:, 0])) % 360
    print(f"  {len(lst):6d} boxes  radii~{rs}  example angles {np.round(ang, 1)}")
