import C17Surv

/-!
# Refinement of survivors (core Lean only)

A box that fails the survivor test `surv` at the box tolerance of the run can be searched again with a finer
tolerance: `survRef P' surv fuel` accepts a box if `surv` does, or if the branch and bound with the finer
parameters `P'` leaves only boxes that `surv` accepts.  The record case of 17 circles uses `P17rf`
(tolerance `2⁻²⁰` instead of `2⁻¹⁸`) for the two regions where survivors fail at `2⁻¹⁸`.
-/

namespace CirclePacking

/-- `surv`, or a finer branch and bound whose survivors all pass `surv` -/
def survRef (P' : Params) (surv : List IBox → Bool) (fuel : Nat) (bx : List IBox) : Bool :=
  surv bx || bnb P' surv fuel bx

/-- the record-case parameters with box tolerance `2⁻²⁰` -/
def P17rf : Params := { P17r with tol := S / 1048576 }

/-- the survivor predicate of the record case, with refinement at tolerance `2⁻²⁰` -/
def survRef17 : List IBox → Bool := survRef P17rf (survOK17h P17r hW17r) 400

/-- the chunk tree of the record case with leaves 48 and 135 of `k7tree` split once more (20 levels, 32
resp. 64 chunks); every other path is a path of `k7tree` -/
def k7tree2 : CTree :=
  .node 22 64 (fun i =>
    if i = 8 then .node 20 32 (fun j =>
      if j = 29 then .node 20 64 (fun l => if l = 11 then .node 20 32 (fun _ => .leaf) else .leaf) else .leaf)
    else if i = 27 then .node 20 32 (fun j => if j = 14 then .node 20 64 (fun _ => .leaf) else .leaf)
    else .leaf)

end CirclePacking
