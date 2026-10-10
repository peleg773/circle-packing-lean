import C15Compute

/-! Computation: the radius-bound runs `m = 8, …, 11` (all `k ≤ m`). Imports only the computational core. -/

namespace CirclePacking

/-- all radius-bound runs -/
def rbAll : Bool :=
  [8, 9, 10, 11].all (fun m => (List.range (m + 1)).all (fun k => checkRun (Prb m k) (fun _ => false) 400))

theorem rbAll_true : rbAll = true := by native_decide

end CirclePacking
