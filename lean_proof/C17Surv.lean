import C17Compute

/-!
# The record case of 17 circles: parameters and survivor predicate (core Lean only)

The record configuration has an interior circle near the centre (point 1, radius 0.109) that blocks no
boundary arc, so the certified arcs are taken from the other six interior circles.  The record case is
searched with box tolerance `2⁻¹⁸`.
-/

namespace CirclePacking

/-- parameters of the record case (`k = 7`) of the main run, `n = 17` -/
def P17r : Params := { P17 7 with tol := S / 262144 }

/-- certified arcs of the interior points with the given indices -/
def survArcsL (P : Params) (bx : List IBox) (js : List Nat) : Option (List (Int × Int)) :=
  if js.all (fun j => arcOK P.ρ (gI bx j) (tOf P (gI bx j))) then
    some (js.map (fun j => arcOf (gI bx j) (tOf P (gI bx j))))
  else none

/-- the interior points of the record that block boundary arcs -/
def arcIdx17 : List Nat := [0, 2, 3, 4, 5, 6]

/-- the survivor predicate for the record case of `n = 17` -/
def survOK17b (P : Params) (bx : List IBox) : Bool :=
  match survArcsL P bx arcIdx17 with
  | none => false
  | some arcs =>
    (List.range 10).all (fun w => (liftArcs arcs).any (fun q => decide (q.1 < (badI17 w).1 ∧ (badI17 w).2 < q.2)) ||
      decide (greedyFromInterval arcs P.δ (badI17 w).1 (badI17 w).2 P.jf 9 < 10)) &&
    (List.range 10).all (fun w => decide ((win17 w).2 - (win17 w).1 < P.δ)) &&
    closeOK17 bx

/-! ### Windows of a given half-width -/

/-- the window of half-width `hW` (units `1/S` turns) around the angle of the boundary point `7 + w` of `c*` -/
def win17h (hW : Int) (w : Nat) : Int × Int := (a17Lo.getD (7 + w) 0 - hW, a17Hi.getD (7 + w) 0 + hW)
def wStart17h (hW : Int) (w : Nat) : Int := if w = 10 then (win17h hW 0).1 + S else (win17h hW w).1
/-- the gap between the windows `w` and `w + 1` -/
def badI17h (hW : Int) (w : Nat) : Int × Int := ((win17h hW w).2, wStart17h hW (w + 1))

/-- closeness to `c*`: interior boxes plus windows, against the uniqueness radius -/
def closeOK17h (hW : Int) (bx : List IBox) : Bool :=
  match sumOpt ((List.range 7).map (fun j => interiorErr17 (gI bx j) j)),
        sumOpt ((List.range 10).map (fun w => boundaryErr17 (win17h hW w) w)) with
  | some ei, some eb => decide (ei + eb < survR2_17)
  | _, _ => false

/-- the survivor predicate for the record case of `n = 17`, with windows of half-width `hW` -/
def survOK17h (P : Params) (hW : Int) (bx : List IBox) : Bool :=
  match survArcsL P bx arcIdx17 with
  | none => false
  | some arcs =>
    (List.range 10).all (fun w =>
      (liftArcs arcs).any (fun q => decide (q.1 < (badI17h hW w).1 ∧ (badI17h hW w).2 < q.2)) ||
      decide (greedyFromInterval arcs P.δ (badI17h hW w).1 (badI17h hW w).2 P.jf 9 < 10)) &&
    (List.range 10).all (fun w => decide ((win17h hW w).2 - (win17h hW w).1 < P.δ)) &&
    closeOK17h hW bx

/-- the window half-width of the record-case certificate (units `1/S` turns, about `3.2·10⁻⁶` turns) -/
def hW17r : Int := 3500000

/-! ### Two-level chunks -/

/-- chunk `i2` of `m2` of the depth-`d2` subtrees of the boxes in chunk `i1` of `m1` of the depth-`d1`
frontier; used where the work of one chunk concentrates in a deep subtree -/
def checkChunk2 (P : Params) (surv : List IBox → Bool) (fuel d1 m1 i1 d2 m2 i2 : Nat) : Bool :=
  paramsOK P && (chunkAux m1 i1 0 (frontier P d1 (rootBox P))).all (fun b =>
    (chunkAux m2 i2 0 (frontier P d2 b)).all (fun b' => bnb P surv fuel b'))

/-! ### Chunk trees -/

/-- a chunk tree: `node d m ch` expands the search tree `d` levels and splits the resulting boxes into `m`
chunks, chunk `i` being handled by `ch i`; a `leaf` runs the branch and bound -/
inductive CTree where
  | leaf : CTree
  | node (d m : Nat) (ch : Nat → CTree) : CTree

/-- the root-to-leaf paths `[(d, m, i), …]` of a chunk tree -/
def CTree.paths : CTree → List (List (Nat × Nat × Nat))
  | .leaf => [[]]
  | .node d m ch => (List.range m).flatMap (fun i => (ch i).paths.map (fun p => (d, m, i) :: p))

/-- every split of the tree has at least one chunk -/
def CTree.posOK : CTree → Bool
  | .leaf => true
  | .node _ m ch => decide (0 < m) && (List.range m).all (fun i => (ch i).posOK)

/-- the computation of one leaf: follow the path, then run the branch and bound -/
def checkPath (P : Params) (surv : List IBox → Bool) (fuel : Nat) : List (Nat × Nat × Nat) → List IBox → Bool
  | [], b => bnb P surv fuel b
  | (d, m, i) :: rest, b => (chunkAux m i 0 (frontier P d b)).all (checkPath P surv fuel rest)

/-- the chunk tree of the record case: depth 22, 64 chunks; chunks 8 and 27 split again (20 levels, 32 chunks), and
sub-chunk 29 of chunk 8 (which holds the neighbourhood of `c*`) once more (20 levels, 64 chunks) -/
def k7tree : CTree :=
  .node 22 64 (fun i =>
    if i = 8 then .node 20 32 (fun j => if j = 29 then .node 20 64 (fun _ => .leaf) else .leaf)
    else if i = 27 then .node 20 32 (fun _ => .leaf)
    else .leaf)

end CirclePacking
