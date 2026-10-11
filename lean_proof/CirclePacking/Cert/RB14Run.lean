import C18Compute

/-! Computation: the radius-bound runs `m = 14` (all `k ≤ 14`), used for `n = 18`. Imports only the
computational core. -/

namespace CirclePacking

/-- all radius-bound runs with 14 circles -/
def rb14All : Bool := (List.range 15).all (fun k => checkRun (Prb14 k) (fun _ => false) 400)

theorem rb14All_true : rb14All = true := by native_decide

end CirclePacking
