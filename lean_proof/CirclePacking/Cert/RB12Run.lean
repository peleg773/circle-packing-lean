import C16Compute

/-! Computation: the radius-bound runs `m = 12` (all `k ≤ 12`), used for `n = 16`. Imports only the
computational core. -/

namespace CirclePacking

/-- all radius-bound runs with 12 circles -/
def rb12All : Bool := (List.range 13).all (fun k => checkRun (Prb12 k) (fun _ => false) 400)

theorem rb12All_true : rb12All = true := by native_decide

end CirclePacking
