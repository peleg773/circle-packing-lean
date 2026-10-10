import json, sys, numpy as np
from search_lib import contact_structure, min_sep
def show(P, title):
    P = np.array(P); d = min_sep(P); rho = 2/d
    r = np.sqrt((P**2).sum(1)); th = np.degrees(np.arctan2(P[:,1], P[:,0])) % 360
    bnd, con = contact_structure(P, d, 1e-6)
    order = np.argsort(th)
    print(f"--- {title}: d={d:.10f} rho(unit circles)={rho:.6f} boundary={len(bnd)} contacts={len(con)}")
    deg = np.zeros(len(P), int)
    for i,j in con: deg[i]+=1; deg[j]+=1
    for i in order:
        print(f"   pt{i:2d} r={r[i]:.5f} (unit-circ {r[i]*rho:.4f}) angle={th[i]:8.3f} deg={deg[i]} {'B' if i in bnd else ' '}")
f = sys.argv[1]; k = int(sys.argv[2]) if len(sys.argv)>2 else 3
data = json.load(open(f))
for c in data['clusters'][:k]:
    show(c['example']['P'], f"n={data['n']} d={c['d']} hits={c['hits']}")
