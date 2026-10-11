import C17Compute

/-! Computation: the radius-bound runs `m = 13` (all `k ≤ 13`), used for `n = 17`. Imports only the
computational core. -/

namespace CirclePacking

/-- all radius-bound runs with 13 circles -/
def rb13All : Bool := (List.range 14).all (fun k => checkRun (Prb13 k) (fun _ => false) 400)

theorem rb13All_true : rb13All = true := by native_decide

end CirclePacking
