"""Rigorous interval primitives for numba (outward rounding via nextafter; IEEE-754 + - * / sqrt are
correctly rounded, so [nextafter(r,-inf), nextafter(r,+inf)] encloses the exact result).
Transcendental functions are NOT taken from libm: cos via Taylor series with explicit remainder,
arccos via the arcsine series (all coefficients positive) with explicit geometric tail bound.
Constants (pi, 2pi, series coefficients) are float brackets computed with arb: rig_consts.json.
"""
import json, os, math
import numpy as np
import numba as nb

_H = os.path.dirname(os.path.abspath(__file__))
_C = json.load(open(os.path.join(_H, "rig_consts.json")))
PI_LO, PI_HI = _C["consts"]["PI"]
TWO_PI_LO, TWO_PI_HI = _C["consts"]["TWO_PI"]
ASIN_LO = np.array([a for a, b in _C["asin"]]); ASIN_HI = np.array([b for a, b in _C["asin"]])
COSC_LO = np.array([a for a, b in _C["cos"]]); COSC_HI = np.array([b for a, b in _C["cos"]])
NASIN = 56
NCOS = 18
INF = np.inf


@nb.njit(cache=True, inline="always")
def dn(x):
    return np.nextafter(x, -INF)


@nb.njit(cache=True, inline="always")
def up(x):
    return np.nextafter(x, INF)


@nb.njit(cache=True)
def imul(al, ah, bl, bh):
    p1 = al * bl; p2 = al * bh; p3 = ah * bl; p4 = ah * bh
    return dn(min(min(p1, p2), min(p3, p4))), up(max(max(p1, p2), max(p3, p4)))


@nb.njit(cache=True)
def isqr(al, ah):
    if al >= 0.0:
        return dn(al * al), up(ah * ah)
    if ah <= 0.0:
        return dn(ah * ah), up(al * al)
    m = max(-al, ah)
    return 0.0, up(m * m)


@nb.njit(cache=True)
def idiv_pos(al, ah, bl, bh):
    # requires bl > 0
    q1 = al / bl; q2 = al / bh; q3 = ah / bl; q4 = ah / bh
    return dn(min(min(q1, q2), min(q3, q4))), up(max(max(q1, q2), max(q3, q4)))


@nb.njit(cache=True)
def asin_series_lo(y):
    """lower bound of arcsin(y) for float y in [0, 0.7072] (partial sum, all terms >= 0, rounded down)."""
    if y <= 0.0:
        return 0.0
    y2 = dn(y * y)
    p = y
    s = 0.0
    for i in range(NASIN):
        s = dn(s + dn(ASIN_LO[i] * p))
        p = dn(p * y2)
    return s


@nb.njit(cache=True)
def asin_series_hi(y):
    """upper bound of arcsin(y) for float y in [0, 0.7072]: partial sum (rounded up) + geometric tail."""
    if y <= 0.0:
        return 0.0
    y2 = up(y * y)
    p = y
    s = 0.0
    for i in range(NASIN):
        s = up(s + up(ASIN_HI[i] * p))
        p = up(p * y2)
    # tail <= a_N y^{2N+1} / (1 - y^2);  p == y^{2N+1} (upper)
    tail = up(up(ASIN_HI[NASIN] * p) / dn(1.0 - y2))
    return up(s + tail)


@nb.njit(cache=True)
def acos_lo(c):
    """rigorous lower bound of arccos(c), c float in [-1, 1]."""
    if c >= 1.0:
        return 0.0
    if c <= -1.0:
        return PI_LO
    if c >= 0.0:
        v = dn(dn(1.0 - c) * 0.5)
        y = dn(math.sqrt(v))
        return dn(2.0 * asin_series_lo(y))
    else:
        # arccos(c) = pi - arccos(-c);  arccos(-c) = 2 asin(sqrt((1+c)/2))
        v = up(up(1.0 + c) * 0.5)
        y = up(math.sqrt(v))
        if y > 0.70711:
            return 0.0    # safe trivial lower bound (cannot happen: y <= sqrt(1/2))
        return dn(PI_LO - up(2.0 * asin_series_hi(y)))


@nb.njit(cache=True)
def acos_hi(c):
    """rigorous upper bound of arccos(c)."""
    if c >= 1.0:
        return 0.0
    if c <= -1.0:
        return PI_HI
    if c >= 0.0:
        v = up(up(1.0 - c) * 0.5)
        y = up(math.sqrt(v))
        if y > 0.70711:
            return PI_HI  # safe trivial upper bound (cannot happen)
        return up(2.0 * asin_series_hi(y))
    else:
        v = dn(dn(1.0 + c) * 0.5)
        y = dn(math.sqrt(v))
        return up(PI_HI - dn(2.0 * asin_series_lo(y)))


@nb.njit(cache=True)
def cos_interval_pt(x):
    """rigorous enclosure [lo, hi] of cos(x) for a float x with |x| <= 40."""
    m = math.floor(x / 6.283185307179586 + 0.5)
    ml, mh = imul(m, m, TWO_PI_LO, TWO_PI_HI)
    rl = dn(x - mh); rh = up(x - ml)
    tl, th = isqr(rl, rh)               # t = r^2 in [tl, th], th <= ~10
    # Horner for sum_{i<N} (-1)^i t^i/(2i)!
    # coefficient intervals s_i
    i = NCOS - 1
    if i % 2 == 0:
        al = COSC_LO[i]; ah = COSC_HI[i]
    else:
        al = -COSC_HI[i]; ah = -COSC_LO[i]
    for ii in range(NCOS - 2, -1, -1):
        pl, ph = imul(tl, th, al, ah)
        if ii % 2 == 0:
            cl = COSC_LO[ii]; ch = COSC_HI[ii]
        else:
            cl = -COSC_HI[ii]; ch = -COSC_LO[ii]
        al = dn(pl + cl); ah = up(ph + ch)
    # remainder |t|^N/(2N)!
    p = 1.0
    for ii in range(NCOS):
        p = up(p * th)
    rem = up(p * COSC_HI[NCOS])
    lo = dn(al - rem); hi = up(ah + rem)
    if lo < -1.0:
        lo = -1.0
    if hi > 1.0:
        hi = 1.0
    return lo, hi


@nb.njit(cache=True)
def cos_min_lo(dlo, dhi):
    """rigorous lower bound of min_{x in [dlo,dhi]} cos x (dlo<=dhi floats)."""
    if dhi - dlo >= 6.0:
        return -1.0
    # does [dlo, dhi] possibly contain an odd multiple of pi?  (2m+1) pi in [(2m+1)PI_LO, (2m+1)PI_HI]
    m0 = math.floor((dlo / 3.141592653589793 - 1.0) / 2.0) - 1
    for m in range(m0, m0 + 4):
        q = 2 * m + 1
        if q >= 0:
            a = dn(q * PI_LO); b = up(q * PI_HI)
        else:
            a = dn(q * PI_HI); b = up(q * PI_LO)
        if b >= dlo and a <= dhi:
            return -1.0
    l1, h1 = cos_interval_pt(dlo)
    l2, h2 = cos_interval_pt(dhi)
    return min(l1, l2)
