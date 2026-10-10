import C16Compute

/-! Computation: the run `n = 16`, `k = 6` (a single run). Imports only the computational core. -/

namespace CirclePacking

theorem n16_k6_run : checkRun (P16 6) (fun _ => false) 400 = true := by native_decide

end CirclePacking
