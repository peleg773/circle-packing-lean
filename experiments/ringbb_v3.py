"""V3 (= ringbb_final.py with a cheaper certified arccos lower bound inside the contraction step only:
rigmath_fast.acos_lo_fast; every other rigorous check unchanged).

FINAL CERTIFIED VERSION (= ringbb_rig_fast.py with: radius-bound table as an input, small survivor buffer whose
overflow is a hard failure, JSON audit log per run).

RIGOROUS branch-and-bound over interior configurations (see ringbb.py docstring and docs/lemmas.md L1-L6).

Every pruning decision and every contraction step is certified with outward-rounded interval
arithmetic (rigmath.py: nextafter-rounding for + - * / sqrt, series enclosures for cos/arccos).
Floating-point (libm) versions from ringbb2.py are used ONLY as fast filters deciding whether a rigorous
check is attempted; a box is discarded only if the rigorous check confirms.

Rigorous inputs: rho_test (an exact double), rigorous float brackets of delta_B = 2 asin(1/rho_test),
R_I = sqrt(rho_test^2 - 4) (upper bound), rho_m lower bounds (from arb), pi, 2pi brackets.

Usage: python ringbb_rig.py n rho_test kmin kmax tol
"""
import sys, os, json, math, time
import numpy as np
import numba as nb
from rigmath_fast import acos_lo_fast
from rigmath import (dn, up, imul, isqr, idiv_pos, acos_lo, acos_hi, cos_min_lo,
                     PI_LO, PI_HI, TWO_PI_LO, TWO_PI_HI)
import ringbb2 as F   # float filters

EPS = 1e-9
HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "out")


def _br(x):
    from flint import arb
    lo = float(x.mid()); hi = lo
    xl = x.mid() - x.rad(); xh = x.mid() + x.rad()
    while arb(lo) > xl:
        lo = math.nextafter(lo, -math.inf)
    while arb(hi) < xh:
        hi = math.nextafter(hi, math.inf)
    return math.nextafter(lo, -math.inf), math.nextafter(hi, math.inf)


def radius_table(mode):
    """lower bounds rho_m (m = 0..39) for the packing-radius pruning rule L6.
    mode 'selfcontained': elementary bounds (m <= 7) + bounds proved by prove_radius_bounds.py (m = 8..13);
    mode 'literature'   : Pirl / Melissen / Fodor values (rounded down)."""
    from flint import arb, ctx
    ctx.prec = 200
    pi = arb.pi()
    if mode == "literature":
        rm = [arb(0), arb(0), arb(1), 2 / arb(3).sqrt(), arb(2).sqrt(), 1 / (pi / 5).sin(), arb(2), arb(2),
              1 / (pi / 7).sin(), 1 / (pi / 8).sin(), arb("2.8130250"), 1 / (pi / 9).sin(), arb("3.0296"),
              1 + arb(5).sqrt()]
        t = [_br(x)[0] for x in rm]
    elif mode == "selfcontained":
        J = json.load(open(os.path.join(os.path.dirname(HERE), "known_packings", "proven_radius_bounds.json")))
        t = list(J["elementary"])
        for m in range(8, 14):
            t.append(float(J["proven"][str(m)]))
    else:
        raise ValueError(mode)
    rmlo = np.zeros(40)
    for i, v in enumerate(t):
        rmlo[i] = v
    for i in range(len(t), 40):
        rmlo[i] = rmlo[i - 1]
    return rmlo


def rigorous_params(n, rho, mode="selfcontained"):
    from flint import arb, ctx
    ctx.prec = 200
    R = arb(rho)   # exact double
    dl, dh = _br(2 * (1 / R).asin())
    ril, rih = _br((R * R - 4).sqrt())
    return dl, dh, rih, radius_table(mode)


@nb.njit(cache=True)
def theta_lo_rig(s, rho):
    """rigorous lower bound of theta_rho(s) (0 if no certain forbidden arc)."""
    if s <= 0.0:
        return 0.0
    s2l, s2h = isqr(s, s)
    r2l, r2h = isqr(rho, rho)
    nl = dn(dn(s2l + r2l) - 4.0); nh = up(up(s2h + r2h) - 4.0)
    dl_, dh_ = imul(2.0 * s, 2.0 * s, rho, rho)
    cl, ch = idiv_pos(nl, nh, dl_, dh_)
    if ch >= 1.0:
        return 0.0
    return acos_lo(ch)


@nb.njit(cache=True)
def maxdist2_hi_rig(sal, sah, pal, pah, sbl, sbh, pbl, pbh):
    dlo = dn(pal - pbh); dhi = up(pah - pbl)
    cm = cos_min_lo(dlo, dhi)
    best = -1.0
    for sa in (sal, sah):
        for sb in (sbl, sbh):
            t1 = up(sa * sa); t2 = up(sb * sb)
            pl, ph = imul(sa, sa, sb, sb)
            ql, qh = imul(pl, ph, cm, cm)
            v = up(up(t1 + t2) - dn(2.0 * ql))
            if v > best:
                best = v
    return best


@nb.njit(cache=True)
def phimin_lo_rig(sal, sah, sbl, sbh):
    """rigorous lower bound of min over radius box of theta_II(sa,sb); returns -1 if no constraint."""
    fmax = -2.0
    for sa in (sal, sah):
        for sb in (sbl, sbh):
            if sa <= 0.0 or sb <= 0.0:
                return -1.0
            s1l, s1h = isqr(sa, sa); s2l, s2h = isqr(sb, sb)
            nh = up(up(s1h + s2h) - 4.0); nl = dn(dn(s1l + s2l) - 4.0)
            dl_, dh_ = imul(2.0 * sa, 2.0 * sa, sb, sb)
            cl, ch = idiv_pos(nl, nh, dl_, dh_)
            if ch > fmax:
                fmax = ch
    if fmax >= 1.0:
        return -1.0
    if fmax < -1.0:
        fmax = -1.0
    return acos_lo_fast(fmax)


@nb.njit(cache=True)
def contract_rig(slo, shi, plo, phi, k):
    """rigorous angular contraction; False => box infeasible.
    (fast variant: the rigorous lower bound pm(a,b) depends only on the radius boxes, which do not change
    during contraction, and is symmetric in (a,b) -> computed at most once per unordered pair.)"""
    PM = np.full((k, k), -3.0)    # -3: not yet computed; -1: no constraint
    for it in range(3):
        changed = False
        for a in range(k):
            wa = phi[a] - plo[a]
            for b in range(k):
                if a == b:
                    continue
                pm = PM[a, b]
                if pm == -3.0:
                    # float filter
                    fmax = -2.0
                    ok = True
                    for sa in (slo[a], shi[a]):
                        for sb in (slo[b], shi[b]):
                            if sa <= 0.0 or sb <= 0.0:
                                ok = False
                            else:
                                f = (sa * sa + sb * sb - 4.0) / (2.0 * sa * sb)
                                if f > fmax:
                                    fmax = f
                    if not ok or fmax >= 1.0 - 1e-12:
                        PM[a, b] = -1.0; PM[b, a] = -1.0
                        continue
                    if fmax < -1.0:
                        fmax = -1.0
                    pmf = 2.0 * math.acos(fmax) - 2e-9
                    if wa >= pmf and (phi[b] - plo[b]) >= pmf:
                        # neither direction can contract now; widths only shrink, so recheck later
                        continue
                    pm = phimin_lo_rig(slo[a], shi[a], slo[b], shi[b])
                    if pm > 0.0:
                        pm = dn(pm - EPS)
                    else:
                        pm = -1.0
                    PM[a, b] = pm; PM[b, a] = pm
                if pm <= 0.0:
                    continue
                if wa >= 2.0 * pm:
                    continue
                exl = up(phi[a] - pm)
                exh = dn(plo[a] + pm)
                for shf in range(-1, 2):
                    if shf == 0:
                        L = exl; H = exh
                    elif shf == 1:
                        L = up(exl + TWO_PI_HI); H = dn(exh + TWO_PI_LO)
                    else:
                        L = up(exl - TWO_PI_LO); H = dn(exh - TWO_PI_HI)
                    if L < plo[b] and plo[b] < H:
                        if phi[b] < H:
                            return False
                        plo[b] = H; changed = True
                    if L < phi[b] and phi[b] < H:
                        if plo[b] > L:
                            return False
                        phi[b] = L; changed = True
                    if plo[b] > phi[b]:
                        return False
        if not changed:
            break
    return True


@nb.njit(cache=True)
def bmax_rig(slo, plo, phi, k, rho, delta_lo):
    """rigorous UPPER bound on the max number of boundary points (certainly-forbidden arcs)."""
    dlt = dn(delta_lo - 2.0 * EPS)
    base_lo = np.empty(k); base_hi = np.empty(k); m = 0
    for j in range(k):
        w = theta_lo_rig(slo[j], rho)
        if w <= 0.0:
            continue
        lo = up(up(phi[j] - w) + EPS)
        hi = dn(dn(plo[j] + w) - EPS)
        if hi <= lo:
            continue
        base_lo[m] = lo; base_hi[m] = hi; m += 1
    if m == 0:
        return int(math.floor(up(TWO_PI_HI / dlt)))
    # lifted (shrunk) arcs, shifts -2..3 periods
    NL = 6 * m
    AL = np.empty(NL); AH = np.empty(NL); c = 0
    for j in range(m):
        for sh in range(-2, 4):
            if sh == 0:
                sl = 0.0; shh = 0.0
            elif sh > 0:
                sl = dn(sh * TWO_PI_LO); shh = up(sh * TWO_PI_HI)
            else:
                sl = dn(sh * TWO_PI_HI); shh = up(sh * TWO_PI_LO)
            AL[c] = up(base_lo[j] + shh); AH[c] = dn(base_hi[j] + sl); c += 1
    best = 0
    for st in range(m):
        a = base_hi[st]
        # skip if a is strictly inside some arc (not allowed)
        inside = False
        for q in range(NL):
            if AL[q] < a and a < AH[q]:
                inside = True
                break
        if inside:
            continue
        limit = up(up(a + TWO_PI_HI) - dlt)
        x = a; count = 1
        while True:
            z = dn(x + dlt)
            moved = True
            while moved:
                moved = False
                for q in range(NL):
                    if AL[q] < z and z < AH[q]:
                        z = AH[q]; moved = True
            if z > limit:
                break
            x = z; count += 1
            if count > 1000:
                break
        if count > best:
            best = count
    return best


@nb.njit(cache=True)
def box_ok_rig(slo, shi, plo, phi, k, n, rho, delta_lo, delta_hi, RI_hi, rhoM):
    # P4 ordering & packing radius bounds (exact float comparisons; rhoM are rigorous lower bounds)
    for j in range(k):
        if shi[j] > RI_hi:
            shi[j] = RI_hi
        lb = rhoM[k - j]
        if slo[j] < lb:
            slo[j] = lb
        if j > 0 and shi[j] > shi[j - 1]:
            shi[j] = shi[j - 1]
        if slo[j] > shi[j]:
            return 4
    for j in range(k - 1, 0, -1):
        if slo[j - 1] < slo[j]:
            slo[j - 1] = slo[j]
        if slo[j - 1] > shi[j - 1]:
            return 4
    # P0 rigorous contraction
    if not contract_rig(slo, shi, plo, phi, k):
        return 1
    # P1 pairwise
    for a in range(k):
        for b in range(a + 1, k):
            if F.maxdist2(slo[a], shi[a], plo[a], phi[a], slo[b], shi[b], plo[b], phi[b]) < 4.0 - 1e-7:
                if maxdist2_hi_rig(slo[a], shi[a], plo[a], phi[a], slo[b], shi[b], plo[b], phi[b]) < 4.0:
                    return 1
    # P2a measure bound
    deltaf = 0.5 * (delta_lo + delta_hi)
    budget = 2.0 * math.pi - (n - k) * deltaf
    tot = 0.0
    for j in range(k):
        e = 2.0 * F.theta_of(slo[j], rho) - deltaf
        if e > 0.0:
            tot += e
    if tot > budget + 1e-7:
        tl = 0.0
        for j in range(k):
            e = dn(dn(2.0 * theta_lo_rig(slo[j], rho)) - delta_hi)
            if e > 0.0:
                tl = dn(tl + e)
        bh = up(TWO_PI_HI - dn((n - k) * delta_lo))
        if tl > bh:
            return 5
    # P2 boundary greedy
    if F.bmax_box(slo, shi, plo, phi, k, rho, deltaf, True) < n - k:
        if bmax_rig(slo, plo, phi, k, rho, delta_lo) < n - k:
            return 2
    return 0


@nb.njit(cache=True)
def run_bb_rig(n, k, rho, delta_lo, delta_hi, RI_hi, rhoM, tol, max_boxes, b0):
    cap = 1 << 16
    stack = np.empty((cap, 4 * k))
    stack[0] = b0; sp = 1
    nproc = 0
    reasons = np.zeros(6, np.int64)
    surv = np.empty((20000, 4 * k)); ns = 0
    while sp > 0:
        sp -= 1
        bx = stack[sp].copy()
        nproc += 1
        if nproc > max_boxes:
            sp += 1
            break
        slo = bx[0:k]; shi = bx[k:2 * k]; plo = bx[2 * k:3 * k]; phi = bx[3 * k:4 * k]
        r = box_ok_rig(slo, shi, plo, phi, k, n, rho, delta_lo, delta_hi, RI_hi, rhoM)
        if r > 0:
            reasons[r] += 1
            continue
        j, c, w = F.choose_split(slo, shi, plo, phi, k)
        if w < tol or sp + 2 >= cap:
            if ns < surv.shape[0]:
                surv[ns] = bx; ns += 1
            else:
                reasons[0] += 1   # overflow marker
            continue
        b1 = bx.copy(); b2 = bx.copy()
        if c == 0:
            mid = 0.5 * (slo[j] + shi[j]); b1[k + j] = mid; b2[j] = mid
        else:
            mid = 0.5 * (plo[j] + phi[j]); b1[3 * k + j] = mid; b2[2 * k + j] = mid
        stack[sp] = b1; sp += 1
        stack[sp] = b2; sp += 1
    return nproc, reasons, surv[:ns], sp


def initial_box(k, RI_hi):
    b0 = np.empty(4 * k)
    for j in range(k):
        b0[j] = 0.0; b0[k + j] = RI_hi; b0[2 * k + j] = 0.0; b0[3 * k + j] = TWO_PI_HI
    b0[2 * k] = 0.0; b0[3 * k] = 0.0
    if k >= 2:
        b0[3 * k + 1] = PI_HI
    return b0


def presplit(n, k, rho, P, target):
    dl, dh, rih, rm = P
    boxes = [initial_box(k, rih)]
    while len(boxes) < target:
        new = []
        for bx in boxes:
            b = bx.copy()
            r = box_ok_rig(b[0:k], b[k:2*k], b[2*k:3*k], b[3*k:4*k], k, n, rho, dl, dh, rih, rm)
            if r > 0:
                continue
            slo = b[0:k]; shi = b[k:2*k]; plo = b[2*k:3*k]; phi = b[3*k:4*k]
            j, c, w = F.choose_split(slo, shi, plo, phi, k)
            b1 = b.copy(); b2 = b.copy()
            if c == 0:
                mid = 0.5 * (slo[j] + shi[j]); b1[k + j] = mid; b2[j] = mid
            else:
                mid = 0.5 * (plo[j] + phi[j]); b1[3 * k + j] = mid; b2[2 * k + j] = mid
            new += [b1, b2]
        if not new:
            break
        boxes = new
    return boxes


def _worker(args):
    n, k, rho, P, tol, maxb, bx = args
    dl, dh, rih, rm = P
    return run_bb_rig(n, k, rho, dl, dh, rih, rm, tol, maxb, bx)


def solve_k(n, k, rho, tol, maxb=int(1e12), nworkers=19, target=4000, mode='selfcontained'):
    from multiprocessing import Pool
    P = rigorous_params(n, rho, mode)
    boxes = presplit(n, k, rho, P, target)
    t0 = time.time()
    with Pool(nworkers) as pool:
        res = pool.map(_worker, [(n, k, rho, P, tol, maxb, b) for b in boxes], chunksize=1)
    nproc = sum(r[0] for r in res)
    reasons = sum(r[1] for r in res)
    surv = np.concatenate([r[2] for r in res]) if any(len(r[2]) for r in res) else np.empty((0, 4 * k))
    unfinished = sum(1 for r in res if r[3] > 0)
    return nproc, reasons, surv, unfinished, time.time() - t0, len(boxes)


def main():
    n = int(sys.argv[1]); rho = float(sys.argv[2]); kmin = int(sys.argv[3]); kmax = int(sys.argv[4])
    tol = float(sys.argv[5]) if len(sys.argv) > 5 else 0.02
    mode = sys.argv[6] if len(sys.argv) > 6 else "selfcontained"
    dl, dh, rih, rm = rigorous_params(n, rho, mode)
    print(f"[FINAL RIGOROUS] n={n} rho_test={rho!r} mode={mode} delta_B in [{dl!r},{dh!r}] R_I <= {rih!r}", flush=True)
    print(f"  radius table (lower bounds rho_m, m=0..13): {list(rm[:14])}", flush=True)
    allok = True
    for k in range(kmin, kmax + 1):
        nproc, reasons, surv, unf, dt, nb0 = solve_k(n, k, rho, tol, mode=mode)
        overflow = int(reasons[0])
        status = "OK" if (overflow == 0 and unf == 0) else "FAIL(overflow/unfinished)"
        if status != "OK":
            allok = False
        print(f"  k={k:2d}: presplit={nb0} boxes={nproc:,} pruned[pair/contr,bnd,-,order,measure]={reasons[1]},{reasons[2]},{reasons[3]},{reasons[4]},{reasons[5]} overflow={overflow} unfinished={unf} survivors={len(surv)} time={dt:.1f}s  [{status}]", flush=True)
        rec = dict(n=n, k=k, rho_test=repr(rho), mode=mode, tol=tol, delta_B=[repr(dl), repr(dh)], R_I_hi=repr(rih),
                   radius_table=[repr(x) for x in rm[:14]], presplit=nb0, boxes=int(nproc),
                   pruned={"pair_or_contraction": int(reasons[1]), "boundary": int(reasons[2]), "order": int(reasons[4]),
                           "measure": int(reasons[5])}, overflow=overflow, unfinished=int(unf), survivors=int(len(surv)),
                   time_s=dt, status=status)
        tag = f"n{n}_k{k}_{mode}"
        json.dump(rec, open(os.path.join(OUT, f"v3_bb_{tag}.json"), "w"), indent=1)
        if len(surv):
            print("      survivor s-ranges: " + ", ".join(f"[{surv[:, j].min():.5f},{surv[:, k + j].max():.5f}]" for j in range(k)), flush=True)
            np.save(os.path.join(OUT, f"v3_surv_{tag}.npy"), surv)
    print("  ALL RUNS COMPLETE WITHOUT OVERFLOW:", allok, flush=True)


if __name__ == "__main__":
    main()
