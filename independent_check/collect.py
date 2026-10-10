"""Collect the result JSON files into a markdown table (printed)."""
import json, glob, os

rows = []
for f in sorted(glob.glob("results/*.json")):
    try:
        r = json.load(open(f))
    except Exception:
        continue
    if isinstance(r, list):
        continue
    st = r.get("stats", {})
    rows.append((os.path.basename(f), r.get("arithmetic", "float64+margins"), r.get("rho"), r.get("k"),
                 r.get("tol"), r.get("nodes"), r.get("survivors"), r.get("done_volume", "-"),
                 st.get("dist"), st.get("excess"), st.get("cap"), st.get("order"),
                 round(r.get("time_s", 0), 1), r.get("use_F4", True), r.get("sym", 0)))
print("| file | arithmetic | rho | k | tol | nodes | unresolved | volume done | pruned dist | pruned excess | pruned capacity | pruned order/count | time s | F4 used | sym |")
print("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|")
for r in rows:
    print("| " + " | ".join(str(x) for x in r) + " |")
