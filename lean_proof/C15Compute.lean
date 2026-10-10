/-!
# Computational part of the circle-packing checker (core Lean only, no Mathlib)

Every definition here is executable; the correctness proofs live in the `CirclePacking.*` modules.

**Number format.** All quantities are integers in units of `2^-40` (the constant `S`): a radius `s`,
an angle `ψ` (in turns), etc. is stored as the integer `s * S`.  Products appearing in certified
tests are compared at the appropriate power of `S`; no rounding happens in certified decisions except
in the explicitly proven `cosZ`.

No floating point is used anywhere.  Heuristics (which certified test to try, with which parameter, where
to split) use 64-bit integers in units of `2^-28`; their results are always re-checked by exact tests.
-/

namespace CirclePacking

/-- the scale `2^40` -/
def S : Int := 1099511627776

/-! ## Certified lower bound for `cos (2 π D / S)` -/

/-- rational lower bound of π (Mathlib `Real.pi_gt_d20`) -/
def piLo : Rat := 314159265358979323846 / 100000000000000000000
/-- rational upper bound of π (Mathlib `Real.pi_lt_d20`) -/
def piHi : Rat := 314159265358979323847 / 100000000000000000000

/-- 8-term cosine partial sum (a lower bound on `[0,1]`). -/
def cosL8 (y : Rat) : Rat :=
  1 - y^2/2 + y^4/24 - y^6/720 + y^8/40320 - y^10/3628800 + y^12/479001600 - y^14/87178291200
/-- 7-term cosine partial sum (an upper bound on `[0,1]`). -/
def cosU7 (y : Rat) : Rat :=
  1 - y^2/2 + y^4/24 - y^6/720 + y^8/40320 - y^10/3628800 + y^12/479001600
/-- 8-term sine partial sum (a lower bound on `[0,1]`). -/
def sinL8 (y : Rat) : Rat :=
  y - y^3/6 + y^5/120 - y^7/5040 + y^9/362880 - y^11/39916800 + y^13/6227020800
    - y^15/1307674368000
/-- 7-term sine partial sum (an upper bound on `[0,1]`). -/
def sinU7 (y : Rat) : Rat :=
  y - y^3/6 + y^5/120 - y^7/5040 + y^9/362880 - y^11/39916800 + y^13/6227020800

def cL8K0 : Int := 87178291200 * 2 ^ 560
def cL8K1 : Int := 43589145600 * 2 ^ 480
def cL8K2 : Int := 3632428800 * 2 ^ 400
def cL8K3 : Int := 121080960 * 2 ^ 320
def cL8K4 : Int := 2162160 * 2 ^ 240
def cL8K5 : Int := 24024 * 2 ^ 160
def cL8K6 : Int := 182 * 2 ^ 80

def cU7K0 : Int := 479001600 * 2 ^ 480
def cU7K1 : Int := 239500800 * 2 ^ 400
def cU7K2 : Int := 19958400 * 2 ^ 320
def cU7K3 : Int := 665280 * 2 ^ 240
def cU7K4 : Int := 11880 * 2 ^ 160
def cU7K5 : Int := 132 * 2 ^ 80

def sL8K0 : Int := 1307674368000 * 2 ^ 560
def sL8K1 : Int := 217945728000 * 2 ^ 480
def sL8K2 : Int := 10897286400 * 2 ^ 400
def sL8K3 : Int := 259459200 * 2 ^ 320
def sL8K4 : Int := 3603600 * 2 ^ 240
def sL8K5 : Int := 32760 * 2 ^ 160
def sL8K6 : Int := 210 * 2 ^ 80

def sU7K0 : Int := 6227020800 * 2 ^ 480
def sU7K1 : Int := 1037836800 * 2 ^ 400
def sU7K2 : Int := 51891840 * 2 ^ 320
def sU7K3 : Int := 1235520 * 2 ^ 240
def sU7K4 : Int := 17160 * 2 ^ 160
def sU7K5 : Int := 156 * 2 ^ 80

/-- `cosL8 (Y / 2^40) * (2^560 * 14!)` -/
def cosL8Num (Y : Int) : Int :=
  let u := Y * Y
  cL8K0 - u * (cL8K1 - u * (cL8K2 - u * (cL8K3 - u * (cL8K4 - u * (cL8K5 - u * (cL8K6 - u))))))
/-- `cosU7 (Y / 2^40) * (2^480 * 12!)` -/
def cosU7Num (Y : Int) : Int :=
  let u := Y * Y
  cU7K0 - u * (cU7K1 - u * (cU7K2 - u * (cU7K3 - u * (cU7K4 - u * (cU7K5 - u)))))
/-- `sinL8 (Y / 2^40) * (2^600 * 15!)` -/
def sinL8Num (Y : Int) : Int :=
  let u := Y * Y
  Y * (sL8K0 - u * (sL8K1 - u * (sL8K2 - u * (sL8K3 - u * (sL8K4 - u * (sL8K5 - u * (sL8K6 - u)))))))
/-- `sinU7 (Y / 2^40) * (2^520 * 13!)` -/
def sinU7Num (Y : Int) : Int :=
  let u := Y * Y
  Y * (sU7K0 - u * (sU7K1 - u * (sU7K2 - u * (sU7K3 - u * (sU7K4 - u * (sU7K5 - u))))))

/-- `⌈2 piHi 2^60⌉` -/
def twoPiHi60 : Int := 7244019458077122843
/-- `⌊2 piLo 2^60⌋` -/
def twoPiLo60 : Int := 7244019458077122842

def cDenL8 : Int := 2 ^ 520 * 87178291200
def cDenU7 : Int := 2 ^ 440 * 479001600
def sDenL8 : Int := 2 ^ 560 * 1307674368000
def sDenU7 : Int := 2 ^ 480 * 6227020800
def two60 : Int := 2 ^ 60

/-- ceiling division (for `b > 0`) -/
def ceilDiv (a b : Int) : Int := -((-a) / b)

/-- certified lower bound of `cos (2 π D / S)` for `0 ≤ D ≤ S/2`, in units of `1/S` -/
def cosZ (D : Int) : Int :=
  if 8 * D ≤ S then
    cosL8Num (ceilDiv (twoPiHi60 * D) two60) / cDenL8
  else if 4 * D ≤ S then
    sinL8Num ((twoPiLo60 * (S - 4 * D)) / (4 * two60)) / sDenL8
  else if S * 3 ≤ 8 * D then
    -(ceilDiv (cosU7Num ((twoPiLo60 * (S - 2 * D)) / (2 * two60))) cDenU7)
  else
    -(ceilDiv (sinU7Num (ceilDiv (twoPiHi60 * (4 * D - S)) (4 * two60))) sDenU7)

/-! ## Greedy placement on the circle (exact, in units of `1/S` turns) -/

/-- Jump out of forbidden arcs: while `z` lies strictly inside an arc of the list, move to its right end. -/
def jump (A : List (Int × Int)) : Nat → Int → Int
  | 0, z => z
  | f + 1, z =>
    match A.find? (fun p => decide (p.1 < z ∧ z < p.2)) with
    | some p => jump A f p.2
    | none => z

/-- Greedy placement after position `x`: number of further points with positions `≤ lim`. -/
def greedyAux (A : List (Int × Int)) (δ lim : Int) (jf : Nat) : Nat → Int → Nat
  | 0, _ => 0
  | f + 1, x =>
    if jump A jf (x + δ) ≤ lim then greedyAux A δ lim jf f (jump A jf (x + δ)) + 1 else 0

/-- Lifted arcs (integer translates by `-1, 0, 1, 2` turns). -/
def liftArcs (base : List (Int × Int)) : List (Int × Int) :=
  base.flatMap (fun p => [(p.1 - S, p.2 - S), p, (p.1 + S, p.2 + S), (p.1 + 2 * S, p.2 + 2 * S)])

/-- `z` lies strictly inside some arc of the list -/
def insideAny (A : List (Int × Int)) (z : Int) : Bool := A.any (fun q => decide (q.1 < z ∧ z < q.2))

/-- Upper bound for the number of points: the greedy count from every arc end that is not strictly
inside another arc (or from `0` if there are no arcs). -/
def greedyBound (base : List (Int × Int)) (δ : Int) (jf f : Nat) : Nat :=
  if base = [] then 1 + greedyAux [] δ (S - δ) jf f 0
  else ((base.filter (fun p => !insideAny (liftArcs base) p.2)).map
    (fun p => 1 + greedyAux (liftArcs base) δ (p.2 + S - δ) jf f p.2)).foldr max 0

/-- greedy count for placements having a point in `[x1, x2]` (mod 1): start at the first allowed point
`≥ x1`, positions up to `x2 + S - δ` -/
def greedyFromInterval (base : List (Int × Int)) (δ x1 x2 : Int) (jf f : Nat) : Nat :=
  1 + greedyAux (liftArcs base) δ (x2 + S - δ) jf f (jump (liftArcs base) jf x1)

/-! ## Boxes and elementary tests -/

/-- Bounds (in units of `1/S`) for the polar coordinates of one interior point. -/
structure IBox where
  slo : Int
  shi : Int
  plo : Int
  phi : Int
deriving Inhabited, Repr, DecidableEq

/-- all four radius corners satisfy `p` -/
def corners (p : Int → Int → Bool) (I J : IBox) : Bool :=
  p I.slo J.slo && p I.slo J.shi && p I.shi J.slo && p I.shi J.shi

/-- bound `D` on the circular distance between angles of `I` and `J` (angles in `[0,S]`), together with
the integer shift realizing it -/
def circBound (I J : IBox) : Option (Int × Int) :=
  if -S ≤ 2 * (I.plo - J.phi) ∧ 2 * (I.phi - J.plo) ≤ S then some (max (J.phi - I.plo) (I.phi - J.plo), 0)
  else if S ≤ 2 * (I.plo - J.phi) then some (S - (I.plo - J.phi), 1)
  else if 2 * (I.phi - J.plo) ≤ -S then some (I.phi - J.plo + S, -1)
  else none

/-- `x² + y² - 2 c x y < 4` at scale `S³` -/
def quadLt4 (c : Int) (x y : Int) : Bool := decide (x * x * S + y * y * S - 2 * c * x * y < 4 * S * S * S)

/-- certified lower bound (units `1/S`) for `cos (2π (ψi - ψj))` over the angle ranges of `I`, `J` -/
def cosLB (I J : IBox) : Int :=
  match circBound I J with
  | some (D, _) => cosZ D
  | none => -S

/-- `true` if every pair of points in the boxes `I`, `J` is at distance `< 2`. -/
def pairTest (I J : IBox) : Bool :=
  decide (0 ≤ I.slo) && decide (0 ≤ J.slo) && corners (quadLt4 (cosLB I J)) I J

/-- `t` is a certified half-width (in units of `1/S` turns) for the box `I`:
`(ρ² + slo² - 4)/(2 ρ slo) ≤ cos (2π t)`. -/
def arcOK (ρ : Int) (I : IBox) (t : Int) : Bool :=
  decide (0 < I.slo) && decide (0 ≤ t) && decide (2 * t ≤ S) &&
    decide ((ρ * ρ + I.slo * I.slo - 4 * S * S) * S ≤ cosZ t * (2 * ρ * I.slo))

/-- the certainly forbidden arc for boundary points -/
def arcOf (I : IBox) (t : Int) : Int × Int := (I.phi - t, I.plo + t)

/-- `(x² + y² - 4)/(2xy) ≤ c` at scale `S³` (for `x, y > 0`) -/
def fLe (c : Int) (x y : Int) : Bool := decide ((x * x + y * y - 4 * S * S) * S ≤ c * (2 * x * y))

/-- `pm` is a certified lower bound (in units of `1/S` turns) for the angle between points of `I` and
`J` at distance `≥ 2`. -/
def pmOK (I J : IBox) (pm : Int) : Bool :=
  decide (0 < I.slo) && decide (0 < J.slo) && decide (0 ≤ pm) && decide (2 * pm ≤ S) &&
    corners (fLe (cosZ pm)) I J

/-- one step: if `lo` lies inside the arc shifted by `m`, move it to the arc's right end -/
def shrinkLo1 (p : Int × Int) (m : Int) (lo : Int) : Int :=
  if p.1 + m < lo ∧ lo < p.2 + m then p.2 + m else lo
/-- one step: if `hi` lies inside the arc shifted by `m`, move it to the arc's left end -/
def shrinkHi1 (p : Int × Int) (m : Int) (hi : Int) : Int :=
  if p.1 + m < hi ∧ hi < p.2 + m then p.1 + m else hi

def shrinkLo (p : Int × Int) (lo : Int) : Int := shrinkLo1 p S (shrinkLo1 p 0 (shrinkLo1 p (-S) lo))
def shrinkHi (p : Int × Int) (hi : Int) : Int := shrinkHi1 p (-S) (shrinkHi1 p 0 (shrinkHi1 p S hi))

/-! ## Fixed-point shadow (heuristics only)

The heuristics below work with 64-bit integers in units of `2^-28` (`QS`).  They only decide which certified
test to try, with which parameter, and where to split a box: every value they produce is either discarded
or re-checked by an exact test, so they need no correctness proof (the soundness theorems hold for any
values they return).  They use no floating point. -/

/-- the heuristic unit `2^28` -/
def QS : Int64 := 268435456

/-- from units `2^-40` to units `2^-28` (heuristic) -/
def toQ (x : Int) : Int64 := Int.toInt64 (x / 4096)

/-- from units `2^-28` back to units `2^-40` -/
def fromQ (x : Int64) : Int := x.toInt * 4096

/-- fixed-point product -/
def qmul (a b : Int64) : Int64 := a * b / QS

/-- `round (2π · 2^28)` -/
def twoPiQ : Int64 := 1686629713

/-- `cos (2π y)` for `0 ≤ y ≤ 1/8` turn (Taylor polynomial) -/
def qcosSmall (y : Int64) : Int64 :=
  let t := qmul y twoPiQ
  let u := qmul t t
  let h := QS - u / 240
  let h := QS - qmul u h / 182
  let h := QS - qmul u h / 132
  let h := QS - qmul u h / 90
  let h := QS - qmul u h / 56
  let h := QS - qmul u h / 30
  let h := QS - qmul u h / 12
  QS - qmul u h / 2

/-- `sin (2π y)` for `0 ≤ y ≤ 1/8` turn (Taylor polynomial) -/
def qsinSmall (y : Int64) : Int64 :=
  let t := qmul y twoPiQ
  let u := qmul t t
  let h := QS - u / 210
  let h := QS - qmul u h / 156
  let h := QS - qmul u h / 110
  let h := QS - qmul u h / 72
  let h := QS - qmul u h / 42
  let h := QS - qmul u h / 20
  let h := QS - qmul u h / 6
  qmul t h

/-- `cos (2π x)` for any `x` (turns) -/
def qcos2pi (x : Int64) : Int64 :=
  let x1 := x % QS
  let x1 := if x1 < 0 then x1 + QS else x1
  let x2 := if x1 > QS / 2 then QS - x1 else x1
  let neg := decide (x2 > QS / 4)
  let y := if neg then QS / 2 - x2 else x2
  let c := if y ≤ QS / 8 then qcosSmall y else qsinSmall (QS / 4 - y)
  if neg then -c else c

/-- integer square root (Newton) -/
def isqrtN (n : Nat) : Nat :=
  if n < 2 then n else go (1 <<< (n.log2 / 2 + 1)) 64
where
  go (x : Nat) : Nat → Nat
    | 0 => x
    | f + 1 => let y := (x + n / x) / 2; if y < x then go y f else x

/-- square root of a nonnegative 64-bit integer -/
def isqrtQ (x : Int64) : Int64 := if x ≤ 0 then 0 else Int.toInt64 (isqrtN x.toInt.toNat : Int)

/-- `asin z` in radians (units `2^-28`) for `0 ≤ z ≤ 1/2` (Taylor polynomial of degree 35, Horner form) -/
def qasinRad (z : Int64) : Int64 :=
  let u := qmul z z
  let h : Int64 := 1041788
  let h := 1138410 + qmul u h
  let h := 1250948 + qmul u h
  let h := 1383331 + qmul u h
  let h := 1540830 + qmul u h
  let h := 1730660 + qmul u h
  let h := 1962941 + qmul u h
  let h := 2252264 + qmul u h
  let h := 2620362 + qmul u h
  let h := 3100913 + qmul u h
  let h := 3748659 + qmul u h
  let h := 4658097 + qmul u h
  let h := 6005481 + qmul u h
  let h := 8155591 + qmul u h
  let h := 11983726 + qmul u h
  let h := 20132659 + qmul u h
  let h := 44739243 + qmul u h
  let h := 268435456 + qmul u h
  qmul z h

/-- `asin z / (2π)` in turns (units `2^-28`) -/
def qasinTurn (z : Int64) : Int64 := qasinRad z * QS / twoPiQ

/-- the `t ∈ [0, 1/2]` turn with `cos (2π t) ≈ f`: `acos f = π/2 - asin f` for `|f| ≤ 1/2`, and the
half-angle formula `acos f = 2 asin √((1 - f)/2)` near `f = ±1` -/
def qacos2pi (f : Int64) : Int64 :=
  if f > QS / 2 then 2 * qasinTurn (isqrtQ ((QS - f) * QS / 2))
  else if f < -(QS / 2) then QS / 2 - 2 * qasinTurn (isqrtQ ((QS + f) * QS / 2))
  else if f ≥ 0 then QS / 4 - qasinTurn f
  else QS / 4 + qasinTurn (-f)

/-- fixed-point copy of a box -/
structure QBox where
  slo : Int64
  shi : Int64
  plo : Int64
  phi : Int64
deriving Inhabited

def toQB (I : IBox) : QBox := ⟨toQ I.slo, toQ I.shi, toQ I.plo, toQ I.phi⟩

/-- bound on the circular distance of the angle ranges (heuristic copy of `circBound`) -/
def circBoundQ (I J : QBox) : Int64 :=
  let dl := I.plo - J.phi
  let dh := I.phi - J.plo
  if -(QS / 2) ≤ dl ∧ dh ≤ QS / 2 then max (-dl) dh
  else if QS / 2 ≤ dl then QS - dl
  else if dh ≤ -(QS / 2) then dh + QS
  else QS / 2

def cornerMaxQ (f : Int64 → Int64 → Int64) (I J : QBox) : Int64 :=
  max (max (f I.slo J.slo) (f I.slo J.shi)) (max (f I.shi J.slo) (f I.shi J.shi))

/-- approximate squared distance of points at radii `u`, `v` whose angle has cosine `c` -/
def qdist2 (c u v : Int64) : Int64 := qmul u u + qmul v v - 2 * qmul (qmul c u) v

/-! ## Branch and bound -/

/-- Parameters of a branch-and-bound run for `n` points, `k` of them interior (lengths in units of
`1/S`). -/
structure Params where
  n : Nat
  k : Nat
  ρ : Int
  Rhi : Int
  δ : Int
  L : Nat → Int
  tol : Int
  jf : Nat
  rounds : Nat

/-- the parameter checks needed for soundness -/
def paramsOK (P : Params) : Bool :=
  decide (0 < P.ρ) && decide (0 ≤ P.Rhi) && decide (P.ρ * P.ρ - 4 * S * S ≤ P.Rhi * P.Rhi) &&
    decide (0 < P.δ) && decide (2 * P.δ ≤ S) &&
    decide ((P.ρ * P.ρ - 2 * S * S) * S ≤ cosZ P.δ * (P.ρ * P.ρ))

/-- entry `j` of a box list -/
def gI (bx : List IBox) (j : Nat) : IBox := bx.getD j default

/-- update every entry, reading from the old list -/
def mapI (bx : List IBox) (f : Nat → IBox → IBox) : List IBox :=
  (List.range bx.length).map (fun j => f j (gI bx j))

def maxSlo (bx : List IBox) : Int := bx.foldl (fun acc I => max acc I.slo) 0

def aSlo (P : Params) (bx : List IBox) (j : Nat) (I : IBox) : Int :=
  if j = 0 then max (max I.slo (maxSlo bx)) (if bx.length < P.n then P.L bx.length else 0) else I.slo
def aShi (P : Params) (bx : List IBox) (j : Nat) (I : IBox) : Int :=
  if j = 0 then min I.shi P.Rhi else min (min I.shi P.Rhi) (gI bx 0).shi
def aPlo (bx : List IBox) (j : Nat) (I : IBox) : Int :=
  if 2 ≤ j then max I.plo (gI bx (j - 1)).plo else I.plo
def aPhi1 (bx : List IBox) (j : Nat) (I : IBox) : Int :=
  if 1 ≤ j ∧ j + 2 ≤ bx.length then min I.phi (gI bx (j + 1)).phi else I.phi
def aPhi2 (bx : List IBox) (j : Nat) (x : Int) : Int :=
  if 3 ≤ bx.length ∧ j = 1 then min x (S - (gI bx (bx.length - 1)).plo) else x
def aPhi3 (bx : List IBox) (j : Nat) (x : Int) : Int :=
  if 3 ≤ bx.length ∧ j = bx.length - 1 then min x (S - (gI bx 1).plo) else x

/-- Step A: radius caps (`s j ≤ s 0`, `s ≤ Rhi`, `s 0 ≥ L k`), angle order, reflection. -/
def stepA (P : Params) (bx : List IBox) : List IBox :=
  mapI bx (fun j I => ⟨aSlo P bx j I, aShi P bx j I, aPlo bx j I, aPhi3 bx j (aPhi2 bx j (aPhi1 bx j I))⟩)

/-- indices whose radius is certainly below `r` -/
def belowL (bx : List IBox) (r : Int) : List Nat :=
  (List.range bx.length).filter (fun i => decide ((gI bx i).shi < r))

def countPrune (P : Params) (bx : List IBox) : Bool :=
  (List.range (bx.length + 1)).any
    (fun m => decide (2 ≤ m) && decide (m < P.n) && decide (m ≤ (belowL bx (P.L m)).length))

def raiseSlo (P : Params) (bx : List IBox) (j : Nat) (x : Int) : Int :=
  (List.range (bx.length + 1)).foldl (fun acc m =>
    if 2 ≤ m ∧ m < P.n ∧ (belowL bx (P.L m)).length + 1 = m ∧ j ∉ belowL bx (P.L m)
    then max acc (P.L m) else acc) x

def countRaise (P : Params) (bx : List IBox) : List IBox :=
  mapI bx (fun j I => ⟨raiseSlo P bx j I.slo, I.shi, I.plo, I.phi⟩)

/-- gate for the pair test (heuristic): try the exact test when the approximate distance is below 2 -/
def pairGate (I J : QBox) : Bool :=
  let c := qcos2pi (circBoundQ I J)
  cornerMaxQ (qdist2 c) I J < 4 * QS + 64

def pairPrune (bx : List IBox) : Bool :=
  let qb := bx.map toQB
  (List.range bx.length).any (fun i => (List.range bx.length).any (fun j =>
    decide (i < j) && pairGate (qb.getD i default) (qb.getD j default) && pairTest (gI bx i) (gI bx j)))

/-- estimate of a certified angular half-width `pm` (heuristic, units `2^-28` turns) -/
def pmGuessQ (I J : QBox) : Int64 :=
  if I.slo ≤ 0 ∨ J.slo ≤ 0 then 0 else
  let f := cornerMaxQ (fun x y =>
    let den := 2 * qmul x y
    if den ≤ 0 then QS else (qmul x x + qmul y y - 4 * QS) * QS / den) I J
  if f ≥ QS then 0 else qacos2pi (max f (-QS)) - 8

/-- would the arc `(l, h)` (mod 1) cut the interval `[lo, hi]` at an end? (heuristic) -/
def cutsQ (l h lo hi : Int64) : Bool :=
  [-QS, 0, QS].any (fun m => decide ((l + m < lo ∧ lo < h + m) ∨ (l + m < hi ∧ hi < h + m)))

/-- angular contraction of `J` by the point box `I`, given a guessed half-width `pm` and a gate `go` -/
def angStepG (I J : IBox) (pm : Int) (go : Bool) : IBox :=
  if go then
    if decide (0 < pm) && decide (I.phi - I.plo < 2 * pm) && pmOK I J pm then
      ⟨J.slo, J.shi, shrinkLo (I.phi - pm, I.plo + pm) J.plo, shrinkHi (I.phi - pm, I.plo + pm) J.phi⟩
    else J
  else J

/-- angular contraction of `J` by the point box `I` -/
def angStep (I J : IBox) (fI fJ : QBox) : IBox :=
  let pmf := pmGuessQ fI fJ
  angStepG I J (fromQ pmf)
    (decide (pmf > 0 ∧ fI.phi - fI.plo < 2 * pmf ∧ cutsQ (fI.phi - pmf) (fI.plo + pmf) fJ.plo fJ.phi = true))

/-- certified radial exclusion: radii in `[u, v]` are at distance `< 2` from every point of `I`
(given a cosine lower bound `c` for the angle difference) -/
def radialOK (I : IBox) (c u v : Int) : Bool :=
  decide (0 ≤ I.slo) && decide (0 ≤ u) && decide (u ≤ v) && corners (quadLt4 c) ⟨u, v, 0, 0⟩ I

/-- shrink a radius interval knowing the radius avoids `[u, v]` -/
def shrinkSlo (lo u v : Int) : Int := if u ≤ lo ∧ lo ≤ v then v else lo
def shrinkShi (hi u v : Int) : Int := if u ≤ hi ∧ hi ≤ v then u else hi

/-- estimate of the radial exclusion interval (heuristic, units `2^-28`) -/
def radGuessQ (I J : QBox) : Option (Int64 × Int64) :=
  let cm := qcos2pi (circBoundQ J I)
  let sm := isqrtQ (QS * QS - cm * cm)
  let one := fun (sb : Int64) =>
    let a := qmul sb cm
    let b := qmul sb sm
    let disc := 4 * QS * QS - b * b
    if disc ≤ 0 then (QS, -QS) else
    let r := isqrtQ disc
    (a - r, a + r)
  let (u1, v1) := one I.slo
  let (u2, v2) := one I.shi
  let u := max (max u1 u2) 0 + 8
  let v := min v1 v2 - 8
  if u < v ∧ ((u ≤ J.slo ∧ J.slo ≤ v) ∨ (u ≤ J.shi ∧ J.shi ≤ v)) then some (u, v) else none

/-- radial contraction of `J` by the point box `I`, given a guessed exclusion interval `g` -/
def radStepG (I J : IBox) (g : Option (Int64 × Int64)) : IBox :=
  match g with
  | none => J
  | some (uf, vf) =>
    let u := fromQ uf + 1
    let v := fromQ vf
    if radialOK I (cosLB J I) u v then
      ⟨shrinkSlo J.slo u v, shrinkShi J.shi u v, J.plo, J.phi⟩
    else J

/-- radial contraction of `J` by the point box `I` -/
def radStep (I J : IBox) (fI fJ : QBox) : IBox := radStepG I J (radGuessQ fI fJ)

def contractPair (I J : IBox) (fI : QBox) : IBox :=
  let J1 := angStep I J fI (toQB J)
  radStep I J1 fI (toQB J1)

def contract (bx : List IBox) : List IBox :=
  let fb := bx.map toQB
  mapI bx (fun j J => (List.range bx.length).foldl
    (fun J' i => if i = j then J' else contractPair (gI bx i) J' (fb.getD i default)) J)

def nonemptyB (bx : List IBox) : Bool :=
  bx.all (fun I => decide (I.slo ≤ I.shi) && decide (I.plo ≤ I.phi))

def round1 (P : Params) (bx : List IBox) : Option (List IBox) :=
  let b1 := stepA P bx
  if countPrune P b1 then none else
  let b2 := countRaise P b1
  if pairPrune b2 then none else
  let b3 := contract b2
  if nonemptyB b3 then some b3 else none

def propagate (P : Params) : Nat → List IBox → Option (List IBox)
  | 0, bx => some bx
  | r + 1, bx =>
    match round1 P bx with
    | none => none
    | some b => if b = bx then some b else propagate P r b

/-! ### Capacity test -/

/-- estimate of a certified half-width of the forbidden arc (heuristic, units `2^-28` turns) -/
def tGuessQ (ρ slo : Int64) : Int64 :=
  if slo ≤ 0 then 0 else
  let den := 2 * qmul ρ slo
  if den ≤ 0 then 0 else
  let g := (qmul ρ ρ + qmul slo slo - 4 * QS) * QS / den
  if g ≥ QS then 0 else qacos2pi (max g (-QS)) - 8

/-- the half-width actually used -/
def tOf (P : Params) (I : IBox) : Int := fromQ (tGuessQ (toQ P.ρ) (toQ I.slo))

/-- certified arcs -/
def arcsOf (P : Params) (bx : List IBox) : List (Int × Int) :=
  bx.filterMap (fun I => if arcOK P.ρ I (tOf P I) then some (arcOf I (tOf P I)) else none)

/-- unverified arcs with the same half-widths (gate) -/
def arcsRaw (P : Params) (bx : List IBox) : List (Int × Int) :=
  bx.filterMap (fun I => if 0 < tOf P I then some (arcOf I (tOf P I)) else none)

def capTest (P : Params) (bx : List IBox) : Bool :=
  decide (greedyBound (arcsRaw P bx) P.δ P.jf (P.n - P.k - 1) < P.n - P.k) &&
    decide (greedyBound (arcsOf P bx) P.δ P.jf (P.n - P.k - 1) < P.n - P.k)

/-! ### Splitting and recursion -/

/-- the box coordinate to split: the widest radius or angle range (angle widths weighted by `2π`
times the radius) -/
def chooseSplit (bx : List IBox) : Nat × Nat :=
  let r := (List.range bx.length).foldl (fun (best : Nat × Nat × Int) j =>
    let I := gI bx j
    let ws := (I.shi - I.slo) * 1000000
    let wa := (I.phi - I.plo) * I.shi * 6283185 / S
    let best := if ws > best.2.2 then (j, 0, ws) else best
    if wa > best.2.2 then (j, 1, wa) else best) (0, 0, -1)
  (r.1, r.2.1)

def splitBox (bx : List IBox) : List IBox × List IBox :=
  let j := (chooseSplit bx).1
  let I := gI bx j
  if (chooseSplit bx).2 = 0 then
    (bx.set j ⟨I.slo, (I.slo + I.shi) / 2, I.plo, I.phi⟩, bx.set j ⟨(I.slo + I.shi) / 2, I.shi, I.plo, I.phi⟩)
  else
    (bx.set j ⟨I.slo, I.shi, I.plo, (I.plo + I.phi) / 2⟩, bx.set j ⟨I.slo, I.shi, (I.plo + I.phi) / 2, I.phi⟩)

/-- the box is still wider than the tolerance in some coordinate (angle widths weighted by the
radius, as in `chooseSplit`) -/
def wide (P : Params) (bx : List IBox) : Bool :=
  bx.any (fun I => decide (P.tol ≤ I.shi - I.slo) || decide (P.tol * S ≤ (I.phi - I.plo) * I.shi * 6))

/-- Branch and bound: `true` means every admissible configuration in the box lies in a box
accepted by `surv`. -/
def bnb (P : Params) (surv : List IBox → Bool) : Nat → List IBox → Bool
  | 0, _ => false
  | f + 1, bx =>
    match propagate P P.rounds bx with
    | none => true
    | some b =>
      if capTest P b then true
      else if wide P b then
        match splitBox b with
        | (b1, b2) => bnb P surv f b1 && bnb P surv f b2
      else surv b

/-- the root box: `s ∈ [0, Rhi]`, `ψ 0 = 0`, other angles in `[0, 1]` turn -/
def rootBox (P : Params) : List IBox :=
  (List.range P.k).map (fun j => if j = 0 then ⟨0, P.Rhi, 0, 0⟩ else ⟨0, P.Rhi, 0, S⟩)

/-- complete check for one value of `k` -/
def checkRun (P : Params) (surv : List IBox → Bool) (fuel : Nat) : Bool :=
  paramsOK P && bnb P surv fuel (rootBox P)

/-! ### Splitting a run into independent chunks (for parallel checking) -/

/-- the open boxes after expanding the search tree to depth `d` (pruned boxes are dropped; boxes below
the tolerance are kept) -/
def frontier (P : Params) : Nat → List IBox → List (List IBox)
  | 0, bx => [bx]
  | d + 1, bx =>
    match propagate P P.rounds bx with
    | none => []
    | some b =>
      if capTest P b then []
      else if wide P b then
        match splitBox b with
        | (b1, b2) => frontier P d b1 ++ frontier P d b2
      else [b]

/-- a hash of a list position (Knuth's multiplicative hash; spreads neighbouring positions over the
chunks) -/
def chunkKey (pos : Nat) : Nat := pos * 2654435761 % 4294967296 / 65536

/-- the elements of a list whose position `pos` has `chunkKey pos % m = i` (positions counted from the
start value) -/
def chunkAux {α : Type} (m i : Nat) : Nat → List α → List α
  | _, [] => []
  | pos, x :: l =>
    if chunkKey pos % m = i then x :: chunkAux m i (pos + 1) l else chunkAux m i (pos + 1) l

/-- chunk `i` of `m` of a run whose search tree is first expanded to depth `d` -/
def checkChunk (P : Params) (surv : List IBox → Bool) (fuel d m i : Nat) : Bool :=
  paramsOK P && (chunkAux m i 0 (frontier P d (rootBox P))).all (fun b => bnb P surv fuel b)

/-! ## Survivors of the record case (`n = 15`, `k = 5`): closeness to `c*` -/

/-- bracket of `α` (angle of the boundary point `p_0` of `c*`), units `1/S` turns -/
def alphaLo : Int := 59563068817
def alphaHi : Int := 59563068822
/-- bracket of `r5 = 1/sin(π/5)` (units `1/S`) -/
def r5Lo : Int := 1870600909919
def r5Hi : Int := 1870600909922
/-- upper bound of `ρ*²` (units `1/S²`) -/
def rho2Hi : Int := 14990625607887442104611697
/-- allowed defect of the container radius: `ρ* - epsR ≤ ρ ≤ ρ*` -/
def epsR : Rat := 1 / 1000000
/-- squared radius of the local uniqueness neighbourhood (= `R2` of the L7 module) -/
def survR2 : Rat := 17 / 5000000

/-- floor and ceiling of `j S / 5` -/
def fifthLo (j : Nat) : Int := (j * S) / 5
def fifthHi (j : Nat) : Int := ceilDiv (j * S) 5

/-- angle brackets (units `1/S`) of the boundary points of `c*`: `w = 2j` is `p_j` at `j/5 + α`,
`w = 2j + 1` is `q_j` at `(j+1)/5 - α` -/
def thetaLo (w : Nat) : Int := if w % 2 = 0 then fifthLo (w / 2) + alphaLo else fifthLo (w / 2 + 1) - alphaHi
def thetaHi (w : Nat) : Int := if w % 2 = 0 then fifthHi (w / 2) + alphaHi else fifthHi (w / 2 + 1) - alphaLo

/-- the certified arcs of the five interior boxes (`none` if some arc is not certified) -/
def survArcs (P : Params) (bx : List IBox) : Option (List (Int × Int)) :=
  if (List.range 5).all (fun j => arcOK P.ρ (gI bx j) (tOf P (gI bx j))) then
    some ((List.range 5).map (fun j => arcOf (gI bx j) (tOf P (gI bx j))))
  else none

/-- window `w < 10` for the boundary points: in the gap after arc `j = w / 2` the first point lies in
`[e_j, b_{j+1} - δ]`, the second in `[e_j + δ, b_{j+1}]` (`e_j` = end of arc `j`, `b_{j+1}` = start of
arc `j + 1`, shifted by `S` for `j = 4`), all enlarged by one unit -/
def win (P : Params) (arcs : List (Int × Int)) (w : Nat) : Int × Int :=
  let j := w / 2
  let e := (arcs.getD j (0, 0)).2
  let b := (arcs.getD ((j + 1) % 5) (0, 0)).1 + (if j = 4 then S else 0)
  if w % 2 = 0 then (e - 1, b - P.δ + 1) else (e + P.δ - 1, b + 1)

/-- start of window `w`, with `wStart 10 = wStart 0 + S` -/
def wStart (P : Params) (arcs : List (Int × Int)) (w : Nat) : Int :=
  if w = 10 then (win P arcs 0).1 + S else (win P arcs w).1

/-- the (closed) bad interval following window `w` -/
def badI (P : Params) (arcs : List (Int × Int)) (w : Nat) : Int × Int :=
  ((win P arcs w).2, wStart P arcs (w + 1))

/-- a bad interval contains no boundary point: it lies inside a forbidden arc, or a point there leaves
room for at most 9 points -/
def badOK (arcs : List (Int × Int)) (δ : Int) (jf : Nat) (x : Int × Int) : Bool :=
  (liftArcs arcs).any (fun q => decide (q.1 < x.1 ∧ x.2 < q.2)) ||
    decide (greedyFromInterval arcs δ x.1 x.2 jf 9 < 10)

/-- squared-distance bound for an interior point of box `I` against `c*`'s interior point `j` -/
def interiorErr (I : IBox) (j : Nat) : Option Rat :=
  let D := max (I.phi - fifthLo j) (fifthHi j - I.plo)
  if 0 ≤ D ∧ 2 * D ≤ S ∧ 0 ≤ I.slo then
    let c := cosZ D
    let f := fun (x y : Int) => x * x * S + y * y * S - 2 * c * x * y
    some (((max (max (f I.slo r5Lo) (f I.slo r5Hi)) (max (f I.shi r5Lo) (f I.shi r5Hi)) : Int) : Rat) /
      ((S * S * S : Int) : Rat))
  else none

/-- squared-distance bound for a boundary point in window `W` against `c*`'s boundary point `w` -/
def boundaryErr (W : Int × Int) (w : Nat) : Option Rat :=
  let D := max (W.2 - thetaLo w) (thetaHi w - W.1)
  if 0 ≤ D ∧ 2 * D ≤ S then
    some (epsR * epsR + ((2 * rho2Hi * (S - cosZ D) : Int) : Rat) / ((S * S * S : Int) : Rat))
  else none

/-- sum of a list of optional rationals (`none` if any entry is `none`) -/
def sumOpt : List (Option Rat) → Option Rat
  | [] => some 0
  | none :: _ => none
  | some x :: l => (sumOpt l).map (x + ·)

/-- the closeness test -/
def closeOK (P : Params) (bx : List IBox) (arcs : List (Int × Int)) : Bool :=
  match sumOpt ((List.range 5).map (fun j => interiorErr (gI bx j) j)),
        sumOpt ((List.range 10).map (fun w => boundaryErr (win P arcs w) w)) with
  | some ei, some eb => decide (ei + eb < survR2)
  | _, _ => false

/-- the survivor predicate for the record case -/
def survOK (P : Params) (bx : List IBox) : Bool :=
  match survArcs P bx with
  | none => false
  | some arcs =>
    (List.range 10).all (fun w => badOK arcs P.δ P.jf (badI P arcs w)) &&
    (List.range 10).all (fun w => decide ((win P arcs w).2 - (win P arcs w).1 < P.δ)) &&
    closeOK P bx arcs

/-! ## The parameters of the proof -/

/-- radius lower bounds (units `1/S`): `Ltab m ≤ ρ_m` (optimal container radius of `m` points) -/
def Ltab (m : Nat) : Int :=
  match m with
  | 0 => 0 | 1 => 0 | 2 => 1099511627776
  | 3 => 1269605398940 | 4 => 1554942701043 | 5 => 1870599039319 | 6 => 2199021056528
  | 7 => 2199021056528 | 8 => 2533862363335 | 9 => 2872875028371 | 10 => 3092645093977
  | _ => 3214435459628

/-- container parameter, interior radius bound and boundary separation of the radius-bound run with
`m` points (`8 ≤ m ≤ 11`) -/
def PrbRho (m : Nat) : Int :=
  match m with | 8 => 2533862363335 | 9 => 2872875028371 | 10 => 3092645093977 | _ => 3214435459628
def PrbRhi (m : Nat) : Int :=
  match m with | 8 => 1258870604101 | 9 => 1848704316591 | 10 => 2174569014505 | _ => 2344545168185
def PrbDelta (m : Nat) : Int :=
  match m with | 8 => 157089945971 | 9 => 137453451915 | 10 => 127211074198 | _ => 122180698426

/-- parameters of the radius-bound run with `m` points (`8 ≤ m ≤ 11`) -/
def Prb (m k : Nat) : Params :=
  { n := m, k := k, ρ := PrbRho m, Rhi := PrbRhi m, δ := PrbDelta m, L := Ltab, tol := S / 16384, jf := 60,
    rounds := 10 }

/-- certified boundary separation (units `1/S` turns) at container parameter `Ltab m`, `3 ≤ m ≤ 6` -/
def smallDelta (m : Nat) : Int :=
  match m with | 3 => 366504481119 | 4 => 274878255930 | 5 => 219902578834 | _ => 183252139027

/-- parameters of the main run, `n = 15` -/
def P15 (k : Nat) : Params where
  n := 15
  k := k
  ρ := 3871772928245
  Rhi := 3186678887092
  δ := 100776187914
  L := Ltab
  tol := S / 16384
  jf := 60
  rounds := 10

/-! ## Instrumentation (development only; not used in any proof) -/

/-- node-limited statistics: (nodes, survivors, pruned by propagation, pruned by capacity, budget left) -/
def bnbLim (P : Params) : Nat → List IBox → Nat → (Nat × Nat × Nat × Nat × Nat)
  | 0, _, b => (0, 0, 0, 0, b)
  | f + 1, bx, budget =>
    if budget = 0 then (0, 0, 0, 0, 0) else
    match propagate P P.rounds bx with
    | none => (1, 0, 1, 0, budget - 1)
    | some b =>
      if capTest P b then (1, 0, 0, 1, budget - 1)
      else if wide P b then
        let (b1, b2) := splitBox b
        let r1 := bnbLim P f b1 (budget - 1)
        let r2 := bnbLim P f b2 r1.2.2.2.2
        (r1.1 + r2.1 + 1, r1.2.1 + r2.2.1, r1.2.2.1 + r2.2.2.1, r1.2.2.2.1 + r2.2.2.2.1, r2.2.2.2.2)
      else (1, 1, 0, 0, budget - 1)

end CirclePacking
