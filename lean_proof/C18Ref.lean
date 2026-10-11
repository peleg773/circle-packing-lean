import C18Tmpl
import C17Ref

/-!
# The survivor tests of the `n = 18` run (core Lean only)

With `k = 7` interior points the survivors lie near the hexagon structure `sHex` or near one of the isolated
structures `s18A`, `s18B`, `s18C` (or a mirror image); with `k = 8`, near `s18K8` or `s18K8b` (or a mirror
image).  The windows of the boundary circles have half-width `hW18`.  A box that fails at the tolerance of the
run (`2⁻¹⁴`) is searched again at tolerance `2⁻¹⁸` (`survRef`).
-/

namespace CirclePacking

/-- half-width of the boundary windows (units `1/S`, about `1.8 · 10⁻⁶` turn) -/
def hW18 : Int := 2000000

/-- the survivor test of the run with `k` interior points (`k = 7` or `k = 8`) -/
def surv18 (k : Nat) (P : Params) (b : List IBox) : Bool :=
  if k = 7 then
    survHex18 P hW18 sHex hexR2s b || survIso18 P hW18 s18A b || survIso18 P hW18 s18B b ||
      survIso18 P hW18 s18C b || survIso18 P hW18 s18Am b || survIso18 P hW18 s18Bm b ||
      survIso18 P hW18 s18Cm b
  else
    survIso18 P hW18 s18K8 b || survIso18 P hW18 s18K8m b || survIso18 P hW18 s18K8b b ||
      survIso18 P hW18 s18K8bm b

/-- the run with `k` interior points at tolerance `2⁻¹⁸` -/
def P18rf (k : Nat) : Params := { P18 k with tol := S / 262144 }

/-- the survivor test with refinement at tolerance `2⁻¹⁸` -/
def survRef18 (k : Nat) : List IBox → Bool := survRef (P18rf k) (surv18 k (P18 k)) 400

end CirclePacking
