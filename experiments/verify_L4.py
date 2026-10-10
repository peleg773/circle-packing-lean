"""Rigorous verification (arb) of lemma L4 at rho = rho_test:
   for all s, t in [E, R_I]:  theta_II(s,t) - theta(s) - theta(t) + delta_B > 0,
where E = sqrt(rho^2-1) - sqrt(3) (pocket threshold), R_I = sqrt(rho^2-4).
2-D bisection; on a box [s1,s2]x[t1,t2]:  theta_II >= arccos(max_{corners} f)  (f max at corners, see docs/lemmas.md),
theta increasing on (rho-2, R_I] -> theta(s) + theta(t) <= theta(s2) + theta(t2).
Usage: python verify_L4.py rho_test
"""
import sys
from flint import arb, ctx
ctx.prec = 128


def main():
    rho = arb(float(sys.argv[1]))
    E = (rho * rho - 1).sqrt() - arb(3).sqrt()
    RI = (rho * rho - 4).sqrt()
    delta = 2 * (1 / rho).asin()
    lo = E.mid() - E.rad() - arb("1e-6").mid()
    hi = RI.mid() + RI.rad()

    def theta(s):
        c = (s * s + rho * rho - 4) / (2 * s * rho)
        return c.acos()

    def f(s, t):
        return (s * s + t * t - 4) / (2 * s * t)
    stack = [(arb(lo), arb(hi), arb(lo), arb(hi))]
    nbox = 0; minmargin = None
    while stack:
        s1, s2, t1, t2 = stack.pop()
        nbox += 1
        fm = None
        for s in (s1, s2):
            for t in (t1, t2):
                v = f(s, t)
                vh = v.mid() + v.rad()
                fm = vh if fm is None or vh > fm else fm
        fm = arb(fm)
        if fm >= 1:
            ok = False
        else:
            if fm < -1:
                fm = arb(-1)
            # theta increasing on (rho-2, R_I]; the domain's right end hi >= R_I: bound theta by theta(R_I ball)
            ts = theta(RI) if s2.mid() + s2.rad() >= RI.mid() - RI.rad() else theta(s2)
            tt = theta(RI) if t2.mid() + t2.rad() >= RI.mid() - RI.rad() else theta(t2)
            marg = fm.acos() - ts - tt + delta
            ok = marg > 0
            if ok:
                mlo = marg.mid() - marg.rad()
                minmargin = mlo if minmargin is None or mlo < minmargin else minmargin
        if not ok:
            if (s2 - s1) < arb("1e-7"):
                print("FAILED near", s1, t1); return
            sm = (s1 + s2) / 2; tm = (t1 + t2) / 2
            sm = arb(sm.mid()); tm = arb(tm.mid())
            stack += [(s1, sm, t1, tm), (sm, s2, t1, tm), (s1, sm, tm, t2), (sm, s2, tm, t2)]
    print(f"L4 VERIFIED at rho={sys.argv[1]} on [{float(lo):.6f}, {float(hi):.6f}]^2 with {nbox} boxes; "
          f"min certified margin {float(minmargin):.5f} rad = {float(minmargin)*57.29578:.3f} deg")


if __name__ == "__main__":
    main()
