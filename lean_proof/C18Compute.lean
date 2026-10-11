import C17Compute

/-!
# Computational part for 18 circles (core Lean only)

The main run `P18` uses the container parameter `ρ = 3.86370330515638`, just above `ρ₁₉ = √6 + √2` (the parameter
of 19 circles); boundary circles then keep the angular gap `δ < 1/12`.  Twelve or more boundary circles (`k ≤ 6`)
are excluded separately: below `ρ₁₉` at most eleven fit.  `Prb14` is the radius-bound run with 14 circles
(`ρ₁₄ > 3.31`).
-/

namespace CirclePacking

/-- radius lower bounds for `n = 18`: as `Ltab17` for `m ≤ 13`, plus `ρ₁₄ > 3.31` (radius-bound run `Prb14`) -/
def Ltab18 (m : Nat) : Int := if m ≤ 13 then Ltab17 m else 3639383487939

/-- the radius-bound run with 14 circles at `3.31` (it uses the bounds `Ltab18 m = Ltab17 m`, `m ≤ 13`) -/
def Prb14 (k : Nat) : Params :=
  { n := 14, k := k, ρ := 3639383487939, Rhi := 2899898083353, δ := 107414144595, L := Ltab18,
    tol := S / 16384, jf := 60, rounds := 10 }

/-- the main run for `n = 18` -/
def P18 (k : Nat) : Params where
  n := 18
  k := k
  ρ := 4248186710296
  Rhi := 3634747177877
  δ := 91625966981
  L := Ltab18
  tol := S / 16384
  jf := 60
  rounds := 10

end CirclePacking
