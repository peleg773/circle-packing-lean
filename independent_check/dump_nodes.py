"""Re-run the float B&B tree (same order as dfs2) in Python, calling the numba node test,
and dump every node's INPUT box (before contraction) with the float decision code.
Used to cross-check the float decisions against the rigorous arb implementation."""
import sys, math, time
import numpy as np
from core import constants, EPS_DB, excess_slack
import bnb2 as BB


def dump(rho, k, tol, out, maxnodes=10 ** 8):
    m = 15 - k
    RI_hi, db_lo, rho_m2 = constants(rho)
    db_hi = db_lo + 2 * EPS_DB
    slack_hi = excess_slack(rho, m, db_lo)
    arc_a = np.empty(k + 2); arc_b = np.empty(k + 2); W = np.empty((8, k + 4))
    stack = [BB.root_box2(k, RI_hi)]
    boxes = []
    codes = []
    n = 0
    while stack and n < maxnodes:
        B0 = stack.pop()
        B = B0.copy()
        code = BB.check_node2(B, k, m, rho, rho_m2, db_lo, db_hi, slack_hi, BB.R_M,
                              arc_a, arc_b, W)
        boxes.append(B0)
        codes.append(code)
        n += 1
        if code != BB.C_ALIVE:
            continue
        best, bi, bd = BB.choose_split(B, k)
        if best < tol:
            continue
        mid = 0.5 * (B[bi, bd] + B[bi, bd + 1])
        B1 = B.copy(); B1[bi, bd + 1] = mid
        B2 = B.copy(); B2[bi, bd] = mid
        stack.append(B1); stack.append(B2)
    np.savez_compressed(out, boxes=np.array(boxes), codes=np.array(codes), rho=rho, k=k)
    return n


if __name__ == "__main__":
    rho = float(sys.argv[1]); k = int(sys.argv[2]); tol = float(sys.argv[3]); out = sys.argv[4]
    t0 = time.time()
    n = dump(rho, k, tol, out)
    print("dumped", n, "nodes in %.1fs" % (time.time() - t0))
