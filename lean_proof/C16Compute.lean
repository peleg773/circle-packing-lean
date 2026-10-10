import C15Compute

/-!
# Computational part for 16 circles (core Lean only)

Parameters of the `n = 16` branch and bound, the radius bound for 12 circles, and the survivor predicate
of the record case `k = 5` (the record configuration `c*` has 5 interior and 11 boundary circles).
-/

namespace CirclePacking

/-- radius lower bounds for `n = 16` (units `1/S`): as `Ltab`, plus `ρ_12 > Ltab16 12` -/
def Ltab16 (m : Nat) : Int :=
  match m with
  | 0 => 0 | 1 => 0 | 2 => 1099511627776
  | 3 => 1269605398940 | 4 => 1554942701043 | 5 => 1870599039319 | 6 => 2199021056528
  | 7 => 2199021056528 | 8 => 2533862363335 | 9 => 2872875028371 | 10 => 3092645093977
  | 11 => 3214435459628
  | _ => 3330749441437

/-- parameters of the radius-bound run with 12 circles -/
def Prb12 (k : Nat) : Params :=
  { n := 12, k := k, ρ := 3330749441437, Rhi := 2501637176567, δ := 117741900755, L := Ltab16,
    tol := S / 16384, jf := 60, rounds := 10 }

/-- parameters of the main run, `n = 16` -/
def P16 (k : Nat) : Params where
  n := 16
  k := k
  ρ := 3975202480924
  Rhi := 3311575378260
  δ := 98082213529
  L := Ltab16
  tol := if k = 5 then S / 131072 else S / 16384
  jf := 60
  rounds := 10

/-! ## Polar brackets of the record configuration `c*` (units `1/S`; points `0..4` interior, `5..15` boundary) -/

def r16Lo : List Int := [1991826275640, 1891696583051, 1792395499758, 1792395499758, 1891696583051,
  3975202478922, 3975202478922, 3975202478922, 3975202478922, 3975202478922, 3975202478922, 3975202478922,
  3975202478922, 3975202478922, 3975202478922, 3975202478922]
def r16Hi : List Int := [1991826279641, 1891696587052, 1792395503759, 1792395503759, 1891696587052,
  3975202482923, 3975202482923, 3975202482923, 3975202482923, 3975202482923, 3975202482923, 3975202482923,
  3975202482923, 3975202482923, 3975202482923, 3975202482923]
def a16Lo : List Int := [-2000, 210501545706, 434190942715, 665320681060, 889010078069, 59344739237,
  157426953767, 255509168297, 353591382827, 451673597357, 549755811888, 647838026418, 745920240948,
  844002455478, 942084670008, 1040166884538]
def a16Hi : List Int := [2001, 210501549707, 434190946716, 665320685061, 889010082070, 59344743238,
  157426957768, 255509172298, 353591386828, 451673601358, 549755815888, 647838030419, 745920244949,
  844002459479, 942084674009, 1040166888539]
/-- upper bound of `ρ*²` (units `1/S²`) -/
def rho2Hi16 : Int := 15802234764338730972437862
/-- squared uniqueness radius (= `n16LU.R2`) -/
def survR2_16 : Rat := 24 / 100000000

/-- half-width of the windows around the boundary angles of `c*` -/
def hW16 : Int := 2097152

def win16 (w : Nat) : Int × Int := (a16Lo.getD (5 + w) 0 - hW16, a16Hi.getD (5 + w) 0 + hW16)
def wStart16 (w : Nat) : Int := if w = 11 then (win16 0).1 + S else (win16 w).1
def badI16 (w : Nat) : Int × Int := ((win16 w).2, wStart16 (w + 1))

/-- squared-distance bound for an interior point of box `I` against `c*`'s point `p` -/
def interiorErr16 (I : IBox) (p : Nat) : Option Rat :=
  let rl := r16Lo.getD p 0
  let rh := r16Hi.getD p 0
  let D := max (I.phi - a16Lo.getD p 0) (a16Hi.getD p 0 - I.plo)
  if 0 ≤ D ∧ 2 * D ≤ S ∧ 0 ≤ I.slo ∧ 0 ≤ rl then
    let c := cosZ D
    let f := fun (x y : Int) => x * x * S + y * y * S - 2 * c * x * y
    some (((max (max (f I.slo rl) (f I.slo rh)) (max (f I.shi rl) (f I.shi rh)) : Int) : Rat) /
      ((S * S * S : Int) : Rat))
  else none

/-- squared-distance bound for a boundary point in window `W` against `c*`'s boundary point `5 + w` -/
def boundaryErr16 (W : Int × Int) (w : Nat) : Option Rat :=
  let D := max (W.2 - a16Lo.getD (5 + w) 0) (a16Hi.getD (5 + w) 0 - W.1)
  if 0 ≤ D ∧ 2 * D ≤ S then
    some (epsR * epsR + ((2 * rho2Hi16 * (S - cosZ D) : Int) : Rat) / ((S * S * S : Int) : Rat))
  else none

def closeOK16 (bx : List IBox) : Bool :=
  match sumOpt ((List.range 5).map (fun j => interiorErr16 (gI bx j) j)),
        sumOpt ((List.range 11).map (fun w => boundaryErr16 (win16 w) w)) with
  | some ei, some eb => decide (ei + eb < survR2_16)
  | _, _ => false

/-- the survivor predicate for the record case of `n = 16` -/
def survOK16 (P : Params) (bx : List IBox) : Bool :=
  match survArcs P bx with
  | none => false
  | some arcs =>
    (List.range 11).all (fun w => (liftArcs arcs).any (fun q => decide (q.1 < (badI16 w).1 ∧ (badI16 w).2 < q.2)) ||
      decide (greedyFromInterval arcs P.δ (badI16 w).1 (badI16 w).2 P.jf 10 < 11)) &&
    (List.range 11).all (fun w => decide ((win16 w).2 - (win16 w).1 < P.δ)) &&
    closeOK16 bx

end CirclePacking
