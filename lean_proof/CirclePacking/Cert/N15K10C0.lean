import C15Compute

/-! Computation: chunk 0 of 8 of the run `n = 15`, `k = 10` (search tree first expanded to depth 16).
Imports only the computational core. -/

namespace CirclePacking

theorem n15_k10_c0 : checkChunk (P15 10) (fun _ => false) 400 16 8 0 = true := by native_decide

end CirclePacking
