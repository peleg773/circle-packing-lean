import C18Compute
import C17Surv

/-!
# Survivor tests for 18 circles (core Lean only)

The survivors of the search at `P18` lie near rigid structures of the 19-circle lattice.  A structure
(`Struct18`) lists its interior points as (radius code, angle in units of `15°`) — radius code `0`: the centre,
`1`: radius `2`, `2`: radius `2√2` — in the labels of its local-uniqueness data, and the angles of its boundary
circles (radius `ρ₁₉`).  The polar brackets used by the tests are computed from these.

* `survIso18`: a whole configuration is rigid; its boundary circles lie one per narrow window (half-width `hW`
  around the lattice angles), as for 17 circles.
* `survHex18`: the hexagon (centre, six ring circles); six wide windows between the ring arcs hold two boundary
  circles each but one, which holds one; the ten pinned circles are within their slots for every choice of the
  short window.

Units: radii and angles in `1/S` (angles in turns).
-/

namespace CirclePacking

/-- the parameters of the `n = 18` run with `k` interior points and box tolerance `t` -/
def P18T (k : Nat) (t : Int) : Params := { P18 k with tol := t }

/-- the start of window `w` (window `K` is window `0` one turn later) -/
def wStartG (win : Nat → Int × Int) (K w : Nat) : Int := if w = K then (win 0).1 + S else (win w).1

/-- the gap between window `w` and window `w + 1` -/
def badIG (win : Nat → Int × Int) (K w : Nat) : Int × Int := ((win w).2, wStartG win K (w + 1))

/-- the `i`-th window other than `m0` (`i < 5`) -/
def hexWin (m0 i : Nat) : Nat := if i < m0 then i else i + 1

/-- slot `s` (`s < 10`) of the hexagon core with short window `m0`: window `hexWin m0 (s / 2)`, left (`s` even)
or right (`s` odd) end; its angle interval -/
def hexSlotLo (win : Nat → Int × Int) (δ : Int) (m0 s : Nat) : Int :=
  if s % 2 = 0 then (win (hexWin m0 (s / 2))).1 else (win (hexWin m0 (s / 2))).1 + δ
def hexSlotHi (win : Nat → Int × Int) (δ : Int) (m0 s : Nat) : Int :=
  if s % 2 = 0 then (win (hexWin m0 (s / 2))).2 - δ else (win (hexWin m0 (s / 2))).2

/-- squared-distance bound between a point of box `I` and a point with radius in `[rl, rh]`, angle in
`[al, ah]` -/
def interiorErrG (I : IBox) (rl rh al ah : Int) : Option Rat :=
  -- the centre (radius `0`): the angle does not matter
  if rl = 0 ∧ rh = 0 then
    if 0 ≤ I.slo then some (((I.shi * I.shi : Int) : Rat) / ((S * S : Int) : Rat)) else none
  else
  let D := max (I.phi - al) (ah - I.plo)
  if 0 ≤ D ∧ 2 * D ≤ S ∧ 0 ≤ I.slo ∧ 0 ≤ rl then
    let c := cosZ D
    let f := fun (x y : Int) => x * x * S + y * y * S - 2 * c * x * y
    some (((max (max (f I.slo rl) (f I.slo rh)) (max (f I.shi rl) (f I.shi rh)) : Int) : Rat) /
      ((S * S * S : Int) : Rat))
  else none

/-- `⌈ρ₁₉² S²⌉` -/
def rho2Hi19 : Int := 18047090325534574755222993

/-- squared-distance bound between a boundary point (angle in `W`, radius in `[ρ₁₉ - epsR, ρ₁₉]`) and the
lattice boundary point with angle in `[al, ah]` -/
def boundaryErrG (W : Int × Int) (al ah : Int) : Option Rat :=
  let D := max (W.2 - al) (ah - W.1)
  if 0 ≤ D ∧ 2 * D ≤ S then
    some (epsR * epsR + ((2 * rho2Hi19 * (S - cosZ D) : Int) : Rat) / ((S * S * S : Int) : Rat))
  else none

/-- radius brackets of the codes `0` (centre), `1` (radius `2`), `2` (radius `2√2`) -/
def radLo (c : Nat) : Int := if c = 0 then 0 else if c = 1 then 2 * S else 3109888511975
def radHi (c : Nat) : Int := if c = 0 then 0 else if c = 1 then 2 * S else 3109888511976

/-- angle brackets of `a · 15°` (turns, units `1/S`) -/
def angLo (a : Nat) : Int := (a * S) / 24
def angHi (a : Nat) : Int := (a * S + 23) / 24

/-- a structure of the 19-circle lattice, in the canonical frame of the search -/
structure Struct18 where
  /-- interior points (radius code, angle in units of `15°`), in the labels of the local-uniqueness data -/
  pts : List (Nat × Nat)
  /-- label of the centre -/
  centre : Nat
  /-- labels of the other interior points, label `0` excluded, in increasing angle -/
  order : List Nat
  /-- angles of the boundary circles, in units of `15°`, increasing -/
  bnd : List Nat
  /-- squared uniqueness radius of the core -/
  R2 : Rat

namespace Struct18
variable (T : Struct18)
def k : Nat := T.pts.length
def code (t : Nat) : Nat := (T.pts.getD t (0, 0)).1
def ang (t : Nat) : Nat := (T.pts.getD t (0, 0)).2
end Struct18

/-- the box index of the centre: the only interior point `j ≥ 1` of radius below `1/2` -/
def findCentre (k : Nat) (bx : List IBox) : Option Nat :=
  match (List.range k).filter (fun j => decide (1 ≤ j) && decide ((gI bx j).shi < S / 2)) with
  | [jc] => some jc
  | _ => none

/-- the structure label of box index `j`, the centre being box index `jc` -/
def tLab (T : Struct18) (jc j : Nat) : Nat :=
  if j = 0 then 0 else if j = jc then T.centre else T.order.getD (if j < jc then j - 1 else j - 2) 0

/-- interior error of a box against a structure -/
def eiOf18 (T : Struct18) (jc : Nat) (bx : List IBox) : Option Rat :=
  sumOpt ((List.range T.k).map (fun j =>
    let t := tLab T jc j
    interiorErrG (gI bx j) (radLo (T.code t)) (radHi (T.code t)) (angLo (T.ang t)) (angHi (T.ang t))))

/-- the box indices other than the centre -/
def nonCentre (k jc : Nat) : List Nat := (List.range k).filter (fun j => j != jc)

/-- **isolated structure**: narrow windows, one boundary circle each -/
def survIso18 (P : Params) (hW : Int) (T : Struct18) (bx : List IBox) : Bool :=
  match findCentre T.k bx with
  | none => false
  | some jc =>
    match survArcsL P bx (nonCentre T.k jc) with
    | none => false
    | some arcs =>
      let B := 18 - T.k
      let win : Nat → Int × Int := fun w => (angLo (T.bnd.getD w 0) - hW, angHi (T.bnd.getD w 0) + hW)
      decide (T.bnd.length = B) &&
      (List.range B).all (fun w =>
        (liftArcs arcs).any (fun q => decide (q.1 < (badIG win B w).1 ∧ (badIG win B w).2 < q.2)) ||
        decide (greedyFromInterval arcs P.δ (badIG win B w).1 (badIG win B w).2 P.jf (B - 1) < B)) &&
      (List.range B).all (fun w => decide ((win w).2 - (win w).1 < P.δ)) &&
      (match eiOf18 T jc bx, sumOpt ((List.range B).map (fun w =>
          boundaryErrG (win w) (angLo (T.bnd.getD w 0)) (angHi (T.bnd.getD w 0)))) with
       | some ei, some eb => decide (ei + eb < T.R2)
       | _, _ => false)

/-- **hexagon**: the structure's boundary angles are the twelve lattice slots (two per window, increasing); the
six windows are `[left slot - hW, right slot + hW]`; `R2s` are the uniqueness radii of the six cores -/
def survHex18 (P : Params) (hW : Int) (T : Struct18) (R2s : List Rat) (bx : List IBox) : Bool :=
  match findCentre T.k bx with
  | none => false
  | some jc =>
    match survArcsL P bx (nonCentre T.k jc) with
    | none => false
    | some arcs =>
      let win : Nat → Int × Int := fun w =>
        (angLo (T.bnd.getD (2 * w) 0) - hW, angHi (T.bnd.getD (2 * w + 1) 0) + hW)
      (List.range 6).all (fun w =>
        (liftArcs arcs).any (fun q => decide (q.1 < (badIG win 6 w).1 ∧ (badIG win 6 w).2 < q.2))) &&
      (List.range 6).all (fun w => decide ((win w).2 - (win w).1 < 2 * P.δ)) &&
      (match eiOf18 T jc bx with
       | none => false
       | some ei => (List.range 6).all (fun m0 =>
          match sumOpt ((List.range 10).map (fun s =>
            let slot := 2 * hexWin m0 (s / 2) + s % 2
            boundaryErrG (hexSlotLo win P.δ m0 s, hexSlotHi win P.δ m0 s) (angLo (T.bnd.getD slot 0))
              (angHi (T.bnd.getD slot 0)))) with
          | some eb => decide (ei + eb < R2s.getD m0 0)
          | none => false))

end CirclePacking
