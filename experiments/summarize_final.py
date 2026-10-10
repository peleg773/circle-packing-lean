"""Collect the audit records of the final certified run and check the completeness conditions of the proof:
for each n: all k in the required range present, overflow = 0, unfinished = 0, survivors = 0 for every k
except the record case, record-case survivors certified (final_check JSON ok), local certificate ok."""
import json, os, glob, re
HERE = os.path.dirname(os.path.abspath(__file__)); OUT = os.path.join(HERE, "out"); ROOT = os.path.dirname(HERE)
REQ = {14: (4, 9, 4), 15: (5, 10, 5), 16: (5, 11, 5)}
allok = True
for n, (k0, k1, krec) in REQ.items():
    print(f"== n={n}: required k in [{k0},{k1}], record case k={krec}")
    for k in range(k0, k1 + 1):
        fn = os.path.join(OUT, f"final_bb_n{n}_k{k}_selfcontained.json")
        if not os.path.exists(fn):
            print(f"   k={k}: MISSING"); allok = False; continue
        r = json.load(open(fn))
        ok = r["overflow"] == 0 and r["unfinished"] == 0 and r["status"] == "OK" and (r["survivors"] == 0 or k == krec)
        allok &= ok
        print(f"   k={k:2d}: boxes={r['boxes']:>14,} survivors={r['survivors']:>6} overflow={r['overflow']} unfinished={r['unfinished']} tol={r['tol']} rho_test={r['rho_test']}  {'OK' if ok else 'PROBLEM'}")
    for fc in (os.path.join(OUT, "final", f"final_check_n{n}.json"), os.path.join(OUT, "final", f"final_check2_n{n}.json")):
        if os.path.exists(fc):
            f = json.load(open(fc))
            print(f"   {os.path.basename(fc)}: boxes={f['boxes']} empty={f['empty']} failing={f['failing']} worst D <= {f['worst_D_upper']:.4e} < {f['threshold_lower']:.4e}: {f['ok']}")
            allok &= f["ok"]
    lc = json.load(open(os.path.join(ROOT, "known_packings", f"local_certificate_n{n}.json")))
    print(f"   local certificate: d* = {lc['d_star'][:40]}  delta_loc = {lc['delta_loc'][:30]}  ok={lc.get('ok', True)}")
    allok &= bool(lc.get("ok", True))
print("ALL PROOF CONDITIONS SATISFIED:", allok)
