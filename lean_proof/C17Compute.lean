import C16Compute

/-!
# Computational part for 17 circles (core Lean only)

Parameters of the `n = 17` branch and bound and of the radius bound for 13 circles.  The record
configuration has 7 interior and 10 boundary circles; `ρ*₁₇ = 3.79203374831057917014912395329569…`.
-/

namespace CirclePacking

/-- radius lower bounds for `n = 17` (units `1/S`): as `Ltab16` for `m ≤ 12`, plus `ρ_13 > Ltab17 13 = 3.23`
(`ρ_13 = 1 + √5`).  Only `m ≤ 13` matters: `Ltab17 13 > Rhi` of `P17`, so `k ≥ 13` closes at the root. -/
def Ltab17 (m : Nat) : Int :=
  if m ≤ 12 then Ltab16 m else 3551422557716

/-- parameters of the radius-bound run with 13 circles -/
def Prb13 (k : Nat) : Params :=
  { n := 13, k := k, ρ := 3551422557716, Rhi := 2788709182580, δ := 110164815533, L := Ltab17,
    tol := S / 16384, jf := 60, rounds := 10 }

/-- parameters of the main run, `n = 17` -/
def P17 (k : Nat) : Params where
  n := 17
  k := k
  ρ := 4169385199188
  Rhi := 3542325459463
  δ := 93399592782
  L := Ltab17
  tol := if k = 7 then S / 131072 else S / 16384
  jf := 60
  rounds := 10

/-! ## Polar brackets of the record configuration `c*` (units `1/S`; points `0..6` interior, `7..16` boundary) -/

def r17Lo : List Int := [2800920444293, 120127137584, 2274240495369, 2140408298927, 2117386499178, 2140408298927,
  2274240495369, 4169385197186, 4169385197186, 4169385197186, 4169385197186, 4169385197186, 4169385197186,
  4169385197186, 4169385197186, 4169385197186, 4169385197186]
def r17Hi : List Int := [2800920448294, 120127141585, 2274240499370, 2140408302928, 2117386503179, 2140408302928,
  2274240499370, 4169385201187, 4169385201187, 4169385201187, 4169385201187, 4169385201187, 4169385201187,
  4169385201187, 4169385201187, 4169385201187, 4169385201187]
def a17Lo : List Int := [-2000, -2000, 152843477751, 359819005401, 549755811888, 739692618375, 946668146025,
  89104959696, 216581995806, 309981589589, 409656421214, 503056014997, 596455608779, 689855202562, 789530034187,
  882929627970, 1010406664080]
def a17Hi : List Int := [2001, 2001, 152843481752, 359819009402, 549755815889, 739692622376, 946668150026,
  89104963697, 216581999807, 309981593590, 409656425215, 503056018998, 596455612780, 689855206563, 789530038188,
  882929631971, 1010406668081]
/-- upper bound of `ρ*²` (units `1/S²`) -/
def rho2Hi17 : Int := 17383772939195380180320921
/-- squared uniqueness radius (= `n17LU.R2`) -/
def survR2_17 : Rat := 89 / 1000000000

/-- half-width of the windows around the boundary angles of `c*` -/
def hW17 : Int := 2097152

def win17 (w : Nat) : Int × Int := (a17Lo.getD (7 + w) 0 - hW17, a17Hi.getD (7 + w) 0 + hW17)
def wStart17 (w : Nat) : Int := if w = 10 then (win17 0).1 + S else (win17 w).1
def badI17 (w : Nat) : Int × Int := ((win17 w).2, wStart17 (w + 1))

/-- squared-distance bound for an interior point of box `I` against `c*`'s point `p` -/
def interiorErr17 (I : IBox) (p : Nat) : Option Rat :=
  let rl := r17Lo.getD p 0
  let rh := r17Hi.getD p 0
  let D := max (I.phi - a17Lo.getD p 0) (a17Hi.getD p 0 - I.plo)
  if 0 ≤ D ∧ 2 * D ≤ S ∧ 0 ≤ I.slo ∧ 0 ≤ rl then
    let c := cosZ D
    let f := fun (x y : Int) => x * x * S + y * y * S - 2 * c * x * y
    some (((max (max (f I.slo rl) (f I.slo rh)) (max (f I.shi rl) (f I.shi rh)) : Int) : Rat) /
      ((S * S * S : Int) : Rat))
  else none

/-- squared-distance bound for a boundary point in window `W` against `c*`'s boundary point `7 + w` -/
def boundaryErr17 (W : Int × Int) (w : Nat) : Option Rat :=
  let D := max (W.2 - a17Lo.getD (7 + w) 0) (a17Hi.getD (7 + w) 0 - W.1)
  if 0 ≤ D ∧ 2 * D ≤ S then
    some (epsR * epsR + ((2 * rho2Hi17 * (S - cosZ D) : Int) : Rat) / ((S * S * S : Int) : Rat))
  else none

def closeOK17 (bx : List IBox) : Bool :=
  match sumOpt ((List.range 7).map (fun j => interiorErr17 (gI bx j) j)),
        sumOpt ((List.range 10).map (fun w => boundaryErr17 (win17 w) w)) with
  | some ei, some eb => decide (ei + eb < survR2_17)
  | _, _ => false

/-- the survivor predicate for the record case of `n = 17` -/
def survOK17 (P : Params) (bx : List IBox) : Bool :=
  match survArcs P bx with
  | none => false
  | some arcs =>
    (List.range 10).all (fun w => (liftArcs arcs).any (fun q => decide (q.1 < (badI17 w).1 ∧ (badI17 w).2 < q.2)) ||
      decide (greedyFromInterval arcs P.δ (badI17 w).1 (badI17 w).2 P.jf 9 < 10)) &&
    (List.range 10).all (fun w => decide ((win17 w).2 - (win17 w).1 < P.δ)) &&
    closeOK17 bx

end CirclePacking
