"""
Branch-and-bound over the k interior centres (polar boxes), version 1.

Symmetry normalisation (sound, see REPORT.md):
  * labels sorted by radius:  s_0 >= s_1 >= ... >= s_{k-1}
  * rotation: point 0 (a point of maximal radius) at angle 0
  * reflection: point 1 has angle in [0, pi]
Necessary conditions used for pruning a box (each proven in REPORT.md):
  (P1) radius ordering + s_i >= r_{k-i} (points i..k-1 lie in the disk of radius s_i)
  (P2) max |P_i - P_j| over the box pair < 2  -> prune
  (P3) angular exclusion between two interior centres (contraction of angle intervals)
  (P4) boundary capacity: with the certainly-forbidden arcs of all points, fewer than
       m = 15-k boundary centres fit -> prune
"""
import math
import numpy as np
from numba import njit
from core import (theta_f, maxdist2, min_ang_sep, remove_arc, capacity_ub,
                  EPS_ARC, EPS_D2, TWO_PI, PI)

# lower bounds r_m (F4), rounded down by 1e-9 for safety; index = number of points
R_M = np.array([0.0, 0.0, 1.0, 2.0 / math.sqrt(3.0), math.sqrt(2.0),
                1.0 / math.sin(math.pi / 5.0), 2.0, 2.0, 2.30476, 2.61312, 2.81302,
                2.92380]) - 1e-9
R_M[0] = 0.0
R_M[1] = 0.0

CODE_ALIVE, CODE_ORDER, CODE_DIST, CODE_ANG, CODE_CAP, CODE_ACCEPT = 0, 1, 2, 3, 4, 5


@njit(cache=True)
def check_node(B, k, m, rho, rho_m2, db, arc_a, arc_b):
    """Contract the box B in place with sound rules; return a code (0 = alive)."""
    for it in range(6):
        changed = False
        for i in range(1, k):
            if B[i, 1] > B[i - 1, 1]:
                B[i, 1] = B[i - 1, 1]
        for i in range(k - 2, -1, -1):
            if B[i, 0] < B[i + 1, 0]:
                B[i, 0] = B[i + 1, 0]
        for i in range(k):
            if B[i, 0] > B[i, 1]:
                return CODE_ORDER
        for i in range(k):
            for j in range(i + 1, k):
                md = maxdist2(B[i, 0], B[i, 1], B[i, 2], B[i, 3],
                              B[j, 0], B[j, 1], B[j, 2], B[j, 3])
                if md < 4.0 - EPS_D2:
                    return CODE_DIST
                D = min_ang_sep(B[i, 0], B[i, 1], B[j, 0], B[j, 1])
                if D < 0.0:
                    return CODE_DIST
                if D > 0.0:
                    if B[j, 3] - B[j, 2] < 2.0 * D:
                        lo, hi, ok = remove_arc(B[i, 2], B[i, 3], B[j, 3] - D, B[j, 2] + D)
                        if not ok:
                            return CODE_ANG
                        if lo > B[i, 2] + 1e-12 or hi < B[i, 3] - 1e-12:
                            changed = True
                        B[i, 2] = lo
                        B[i, 3] = hi
                    if B[i, 3] - B[i, 2] < 2.0 * D:
                        lo, hi, ok = remove_arc(B[j, 2], B[j, 3], B[i, 3] - D, B[i, 2] + D)
                        if not ok:
                            return CODE_ANG
                        if lo > B[j, 2] + 1e-12 or hi < B[j, 3] - 1e-12:
                            changed = True
                        B[j, 2] = lo
                        B[j, 3] = hi
        if not changed:
            break
    n = 0
    for i in range(k):
        th = theta_f(B[i, 0], rho, rho_m2)
        if th > 0.0:
            w = B[i, 3] - B[i, 2]
            if w < 2.0 * th - 2.0 * EPS_ARC:
                arc_a[n] = B[i, 3] - th + EPS_ARC
                arc_b[n] = B[i, 2] + th - EPS_ARC
                n += 1
    cap = capacity_ub(arc_a, arc_b, n, db, m)
    if cap < m:
        return CODE_CAP
    return CODE_ALIVE


@njit(cache=True)
def choose_split(B, k):
    best = -1.0
    bi = -1
    bd = -1
    for i in range(k):
        ws = B[i, 1] - B[i, 0]
        wa = (B[i, 3] - B[i, 2]) * B[i, 1]
        if ws > best:
            best = ws
            bi = i
            bd = 0
        if wa > best:
            best = wa
            bi = i
            bd = 2
    return best, bi, bd


@njit(cache=True)
def dfs(stack_in, k, m, rho, rho_m2, db, tol, max_nodes, surv, stats):
    STACK = 200000
    stack = np.empty((STACK, k, 4))
    n0 = stack_in.shape[0]
    for i in range(n0):
        stack[i] = stack_in[i]
    sp = n0
    nsurv = 0
    nodes = 0
    arc_a = np.empty(k + 1)
    arc_b = np.empty(k + 1)
    B = np.empty((k, 4))
    maxsurv = surv.shape[0]
    while sp > 0 and nodes < max_nodes:
        sp -= 1
        for i in range(k):
            for t in range(4):
                B[i, t] = stack[sp, i, t]
        nodes += 1
        code = check_node(B, k, m, rho, rho_m2, db, arc_a, arc_b)
        stats[code] += 1
        if code != CODE_ALIVE:
            continue
        best, bi, bd = choose_split(B, k)
        if best < tol:
            if nsurv < maxsurv:
                for i in range(k):
                    for t in range(4):
                        surv[nsurv, i, t] = B[i, t]
            nsurv += 1
            continue
        if sp + 2 > STACK:
            # should not happen; treat as survivor so nothing is lost
            if nsurv < maxsurv:
                for i in range(k):
                    for t in range(4):
                        surv[nsurv, i, t] = B[i, t]
            nsurv += 1
            stats[7] += 1
            continue
        mid = 0.5 * (B[bi, bd] + B[bi, bd + 1])
        for i in range(k):
            for t in range(4):
                stack[sp, i, t] = B[i, t]
                stack[sp + 1, i, t] = B[i, t]
        stack[sp, bi, bd + 1] = mid      # lower half
        stack[sp + 1, bi, bd] = mid      # upper half
        sp += 2
    return nodes, nsurv, stack[:sp].copy()


def root_box(k, RI_hi):
    B = np.zeros((k, 4))
    for i in range(k):
        B[i, 0] = R_M[k - i]
        B[i, 1] = RI_hi
        B[i, 2] = 0.0
        B[i, 3] = TWO_PI + 1e-9
    B[0, 2] = 0.0
    B[0, 3] = 0.0
    if k > 1:
        B[1, 2] = 0.0
        B[1, 3] = PI + 1e-9
    return B
