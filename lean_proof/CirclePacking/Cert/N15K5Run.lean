import C15Compute

/-! Computation: the run `n = 15`, `k = 5` (a single run). Imports only the computational core. -/

namespace CirclePacking

theorem n15_k5_run : checkRun (P15 5) (survOK (P15 5)) 400 = true := by native_decide

end CirclePacking
