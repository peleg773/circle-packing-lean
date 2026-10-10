"""
Branch-and-bound over the k interior centres (polar boxes), version 2.

Symmetry normalisation (sound, see REPORT.md):
  * point 0 is a point of maximal radius and sits at angle 0 (rotation)
  * points 1..k-1 are labelled by increasing angle in [0, 2pi]   (permutation)
  * psi_1 + psi_{k-1} <= 2pi                                        (reflection)
Sound pruning / contraction rules:
  (R1) s_i <= s_0 ; s_0 >= r_k ; counting rule: #{i : s_i < r_n} <= n-1 (F4)
  (R2) max |P_i - P_j| over the box pair < 2  -> prune
  (R3) angular exclusion between interior centres (contract angle intervals)
  (R4) radial exclusion between interior centres (contract radius intervals)
  (R5) excess bound: sum_i (2 theta(s_i) - delta_B)^+ <= 2pi - m delta_B
  (R6) boundary capacity with the certainly-forbidden arcs < m -> prune
"""
import math
import numpy as np
from numba import njit
from core import (theta_f, maxdist2, min_ang_sep, remove_arc, capacity_ws, cos_min_interval,
                  radial_forbidden, EPS_ARC, EPS_D2, TWO_PI, PI)

R_M = np.array([0.0, 0.0, 1.0, 2.0 / math.sqrt(3.0), math.sqrt(2.0),
                1.0 / math.sin(math.pi / 5.0), 2.0, 2.0, 2.30476, 2.61312, 2.81302,
                2.92380, 0.0, 0.0, 0.0, 0.0]) - 1e-9
R_M[0] = 0.0
R_M[1] = 0.0
R_M[12:] = 0.0      # r_12..r_15 not used (no bound)

import os
USE_R5 = os.environ.get('IC_R5','1')=='1'
USE_R4 = os.environ.get('IC_R4','1')=='1'
USE_R3 = os.environ.get('IC_R3','1')=='1'
(C_ALIVE, C_ORDER, C_DIST, C_ANG, C_RAD, C_EXCESS, C_CAP, C_ACCEPT) = range(8)
NSTAT = 10


@njit(cache=True)
def pair_contract(B, i, j):
    """Apply R2-R4 to the pair (i, j).  Returns (code, changed)."""
    changed = False
    md = maxdist2(B[i, 0], B[i, 1], B[i, 2], B[i, 3], B[j, 0], B[j, 1], B[j, 2], B[j, 3])
    if md < 4.0 - EPS_D2:
        return C_DIST, changed
    # R3 angular
    D = min_ang_sep(B[i, 0], B[i, 1], B[j, 0], B[j, 1])
    if D < 0.0:
        return C_DIST, changed
    if D > 0.0 and USE_R3:
        if B[j, 3] - B[j, 2] < 2.0 * D:
            lo, hi, ok = remove_arc(B[i, 2], B[i, 3], B[j, 3] - D, B[j, 2] + D)
            if not ok:
                return C_ANG, changed
            if lo > B[i, 2] + 1e-12 or hi < B[i, 3] - 1e-12:
                changed = True
            B[i, 2] = lo
            B[i, 3] = hi
        if B[i, 3] - B[i, 2] < 2.0 * D:
            lo, hi, ok = remove_arc(B[j, 2], B[j, 3], B[i, 3] - D, B[i, 2] + D)
            if not ok:
                return C_ANG, changed
            if lo > B[j, 2] + 1e-12 or hi < B[j, 3] - 1e-12:
                changed = True
            B[j, 2] = lo
            B[j, 3] = hi
    # R4 radial
    cm = cos_min_interval(B[i, 2] - B[j, 3], B[i, 3] - B[j, 2])
    for rep in range(2 if USE_R4 else 0):
        if rep == 0:
            a = i
            b = j
        else:
            a = j
            b = i
        u, v = radial_forbidden(B[b, 0], B[b, 1], cm)
        if u < v:
            lo = B[a, 0]
            hi = B[a, 1]
            if u < lo and v > lo:
                lo = v
            if u < hi and v > hi:
                hi = u
            if lo > hi:
                return C_RAD, changed
            if lo > B[a, 0] + 1e-12 or hi < B[a, 1] - 1e-12:
                changed = True
            B[a, 0] = lo
            B[a, 1] = hi
    return C_ALIVE, changed


@njit(cache=True)
def check_node2(B, k, m, rho, rho_m2, db_lo, db_hi, slack_hi, rm, arc_a, arc_b, W, sym=0):
    for it in range(10):
        changed = False
        # R1: point 0 has maximal radius
        for i in range(1, k):
            if B[i, 1] > B[0, 1]:
                B[i, 1] = B[0, 1]
            if B[0, 0] < B[i, 0]:
                B[0, 0] = B[i, 0]
        if B[0, 0] < rm[k]:
            B[0, 0] = rm[k]
        # angle ordering of 1..k-1   (sym=1: no permutation/reflection breaking)
        if sym == 0:
            for i in range(2, k):
                if B[i, 2] < B[i - 1, 2]:
                    B[i, 2] = B[i - 1, 2]
            for i in range(k - 2, 0, -1):
                if B[i, 3] > B[i + 1, 3]:
                    B[i, 3] = B[i + 1, 3]
        # reflection
        if k >= 3 and sym == 0:
            t = TWO_PI + 1e-9 - B[k - 1, 2]
            if B[1, 3] > t:
                B[1, 3] = t
            t = TWO_PI + 1e-9 - B[1, 2]
            if B[k - 1, 3] > t:
                B[k - 1, 3] = t
        # counting rule
        for n in range(2, k + 1):
            cnt = 0
            for i in range(k):
                if B[i, 1] < rm[n]:
                    cnt += 1
            if cnt >= n:
                return C_ORDER
            if cnt == n - 1:
                for i in range(k):
                    if B[i, 1] >= rm[n] and B[i, 0] < rm[n]:
                        B[i, 0] = rm[n]
                        changed = True
        for i in range(k):
            if B[i, 0] > B[i, 1] or B[i, 2] > B[i, 3]:
                return C_ORDER
        for i in range(k):
            for j in range(i + 1, k):
                code, ch = pair_contract(B, i, j)
                if code != C_ALIVE:
                    return code
                if ch:
                    changed = True
        if not changed:
            break
    # R5 excess bound
    ex = 0.0
    for i in range(k):
        th = theta_f(B[i, 0], rho, rho_m2)
        e = 2.0 * th - 2e-12 - db_hi
        if e > 0.0:
            ex += e
    if USE_R5 and ex > slack_hi + 1e-9:
        return C_EXCESS
    # R6 capacity
    n = 0
    for i in range(k):
        th = theta_f(B[i, 0], rho, rho_m2)
        if th > 0.0:
            w = B[i, 3] - B[i, 2]
            if w < 2.0 * th - 2.0 * EPS_ARC:
                arc_a[n] = B[i, 3] - th + EPS_ARC
                arc_b[n] = B[i, 2] + th - EPS_ARC
                n += 1
    cap = capacity_ws(arc_a, arc_b, n, db_lo, m, W)
    if cap < m:
        return C_CAP
    return C_ALIVE


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
def dfs2(stack_in, vol_in, k, m, rho, rho_m2, db_lo, db_hi, slack_hi, rm, tol, max_nodes,
         surv, stats, accept_fn_flag, pent, stop_at=1 << 62, sym=0):
    """Depth-first B&B.  Returns (nodes, nsurv, done_volume, remaining boxes, their volumes).
    accept_fn_flag=1: boxes contained in the pentagon neighbourhood `pent` are accepted."""
    STACK = 100000
    stack = np.empty((STACK, k, 4))
    vol = np.empty(STACK)
    n0 = stack_in.shape[0]
    for i in range(n0):
        stack[i] = stack_in[i]
        vol[i] = vol_in[i]
    sp = n0
    nsurv = 0
    nodes = 0
    done = 0.0
    arc_a = np.empty(k + 2)
    arc_b = np.empty(k + 2)
    W = np.empty((8, k + 4))
    B = np.empty((k, 4))
    maxsurv = surv.shape[0]
    while sp > 0 and nodes < max_nodes and nsurv < stop_at:
        sp -= 1
        for i in range(k):
            for t in range(4):
                B[i, t] = stack[sp, i, t]
        v = vol[sp]
        nodes += 1
        code = check_node2(B, k, m, rho, rho_m2, db_lo, db_hi, slack_hi, rm, arc_a, arc_b, W,
                           sym)
        if code == C_ALIVE and accept_fn_flag == 1:
            if in_pentagon_nbhd(B, k, pent):
                code = C_ACCEPT
        stats[code] += 1
        if code != C_ALIVE:
            done += v
            continue
        best, bi, bd = choose_split(B, k)
        if best < tol or sp + 2 > STACK:
            if nsurv < maxsurv:
                for i in range(k):
                    for t in range(4):
                        surv[nsurv, i, t] = B[i, t]
            nsurv += 1
            stats[9] += 1
            done += v
            continue
        mid = 0.5 * (B[bi, bd] + B[bi, bd + 1])
        for i in range(k):
            for t in range(4):
                stack[sp, i, t] = B[i, t]
                stack[sp + 1, i, t] = B[i, t]
        stack[sp, bi, bd + 1] = mid
        stack[sp + 1, bi, bd] = mid
        vol[sp] = 0.5 * v
        vol[sp + 1] = 0.5 * v
        sp += 2
    return nodes, nsurv, done, stack[:sp].copy(), vol[:sp].copy()


@njit(cache=True)
def in_pentagon_nbhd(B, k, pent):
    """pent = [r5, eps, phi0]: True if every point of box i lies within eps of a vertex
    r5*exp(i(phi0 + 2 pi j/5)), with distinct vertices for distinct i."""
    r5 = pent[0]
    eps = pent[1]
    used = np.zeros(5, dtype=np.bool_)
    for i in range(k):
        found = False
        for j in range(5):
            if used[j]:
                continue
            ang = pent[2] + TWO_PI * j / 5.0
            for sh in (-TWO_PI, 0.0, TWO_PI):
                md = maxdist2(B[i, 0], B[i, 1], B[i, 2], B[i, 3], r5, r5, ang + sh, ang + sh)
                if md <= eps * eps:
                    found = True
                    break
            if found:
                used[j] = True
                break
        if not found:
            return False
    return True


def root_box2(k, RI_hi, rm=None):
    if rm is None:
        rm = R_M
    B = np.zeros((k, 4))
    for i in range(k):
        B[i, 0] = 0.0
        B[i, 1] = RI_hi
        B[i, 2] = 0.0
        B[i, 3] = TWO_PI + 1e-9
    B[0, 0] = rm[k]
    B[0, 2] = 0.0
    B[0, 3] = 0.0
    return B
