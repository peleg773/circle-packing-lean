import C15Compute

/-! Computation: the run `n = 15`, `k = 6` (a single run). Imports only the computational core. -/

namespace CirclePacking

theorem n15_k6_run : checkRun (P15 6) (fun _ => false) 400 = true := by native_decide

end CirclePacking
