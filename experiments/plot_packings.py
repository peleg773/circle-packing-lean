"""Draw the record packings (unit-circle normalisation) with contact graph; boundary circles shaded."""
import json, os, numpy as np, matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
D = json.load(open(os.path.join(ROOT, "known_packings", "known_packings_13_20.json")))
fig, axes = plt.subplots(2, 4, figsize=(20, 10.5))
for ax, n in zip(axes.flat, range(13, 21)):
    E = D[str(n)]
    P = np.array([[float(a), float(b)] for a, b in E["points"]]); d = float(E["d"]); rho = 2 / d
    C = P * rho
    ax.add_patch(plt.Circle((0, 0), rho + 1, fill=False, lw=1.5, color="k"))
    for i, (x, y) in enumerate(C):
        b = i in E["boundary"]
        ax.add_patch(plt.Circle((x, y), 1, fc="#cfe2f3" if b else "#f9cb9c", ec="#555", lw=0.8))
        ax.text(x, y, str(i), ha="center", va="center", fontsize=7)
    for i, j in E["contacts"]:
        ax.plot([C[i, 0], C[j, 0]], [C[i, 1], C[j, 1]], color="#c00", lw=1.2)
    ax.set_xlim(-rho - 1.2, rho + 1.2); ax.set_ylim(-rho - 1.2, rho + 1.2); ax.set_aspect("equal"); ax.axis("off")
    ax.set_title(f"n={n}: R={1+rho:.6f}, d={d:.9f}\n{len(E['boundary'])} boundary, {len(E['contacts'])} contacts", fontsize=10)
plt.suptitle("Best-known packings (Packomania), unit circles; blue = touching container, orange = interior; red = contacts")
plt.tight_layout()
out = os.path.join(ROOT, "known_packings", "packings_13_20.png")
plt.savefig(out, dpi=110)
print(out)
