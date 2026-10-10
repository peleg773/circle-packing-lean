"""Alternative split heuristics (exploration).  conflict-directed: split a coordinate of the pair whose
max-distance upper bound is smallest (closest to infeasible), choosing the wider (s or s*psi) coordinate of the
two points; fall back to the widest coordinate if no pair has maxdist^2 < THRESH."""
import math
import numpy as np
import numba as nb
import ringbb2 as F


@nb.njit(cache=True)
def choose_split_conflict(slo, shi, plo, phi, k, thresh):
    best = 1e300; ba = -1; bb = -1
    for a in range(k):
        for b in range(a + 1, k):
            v = F.maxdist2(slo[a], shi[a], plo[a], phi[a], slo[b], shi[b], plo[b], phi[b])
            if v < best:
                best = v; ba = a; bb = b
    if best < thresh:
        bw = -1.0; bj = -1; bc = 0
        for j in (ba, bb):
            ws = shi[j] - slo[j]
            wp = (phi[j] - plo[j]) * shi[j]
            if ws > bw:
                bw = ws; bj = j; bc = 0
            if wp > bw:
                bw = wp; bj = j; bc = 1
        if bw > 1e-3:
            return bj, bc, bw
    return F.choose_split(slo, shi, plo, phi, k)


@nb.njit(cache=True)
def choose_split_deep_last(slo, shi, plo, phi, k, deep_r, wdeep):
    """widest-first, but widths of points that may be deep (s_lo <= deep_r) are down-weighted by wdeep."""
    best = -1.0; bj = -1; bc = 0; braw = 0.0
    for j in range(k):
        f = wdeep if slo[j] <= deep_r else 1.0
        ws = shi[j] - slo[j]
        wp = (phi[j] - plo[j]) * shi[j]
        if ws * f > best:
            best = ws * f; bj = j; bc = 0; braw = ws
        if wp * f > best:
            best = wp * f; bj = j; bc = 1; braw = wp
    return bj, bc, braw
