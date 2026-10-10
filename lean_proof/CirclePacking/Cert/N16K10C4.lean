import C16Compute

/-! Computation: chunk 4 of 14 of the run `n = 16`, `k = 10` (search tree first expanded to depth 16).
Imports only the computational core. -/

namespace CirclePacking

theorem n16_k10_c4 : checkChunk (P16 10) (fun _ => false) 400 16 14 4 = true := by native_decide

end CirclePacking
