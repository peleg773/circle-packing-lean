"""Cheaper rigorous arccos LOWER bound for the contraction step (any valid lower bound is sound there).
arccos(c) = 2 asin(y), y = sqrt((1-c)/2) for c >= 0: the partial sum of the arcsine series (positive terms,
rounded down) is a valid lower bound for ANY number of terms; we use NF = 12 terms.
For c < 0: arccos(c) = pi - 2 asin(y'), y' = sqrt((1+c)/2) <= 1/sqrt2, and we need an UPPER bound of asin(y'):
partial sum (rounded up) + geometric tail a_NF y'^(2NF+1)/(1 - y'^2) (coefficients decreasing)."""
import math
import numpy as np
import numba as nb
from rigmath import dn, up, PI_LO, ASIN_LO, ASIN_HI

NF = 12


@nb.njit(cache=True)
def acos_lo_fast(c):
    if c >= 1.0:
        return 0.0
    if c <= -1.0:
        return PI_LO
    if c >= 0.0:
        y = dn(math.sqrt(dn(dn(1.0 - c) * 0.5)))
        if y <= 0.0:
            return 0.0
        y2 = dn(y * y); p = y; s = 0.0
        for i in range(NF):
            s = dn(s + dn(ASIN_LO[i] * p)); p = dn(p * y2)
        return dn(2.0 * s)
    else:
        y = up(math.sqrt(up(up(1.0 + c) * 0.5)))
        if y > 0.70711:
            return 0.0
        y2 = up(y * y); p = y; s = 0.0
        for i in range(NF):
            s = up(s + up(ASIN_HI[i] * p)); p = up(p * y2)
        tail = up(up(ASIN_HI[NF] * p) / dn(1.0 - y2))
        return dn(PI_LO - up(2.0 * up(s + tail)))
