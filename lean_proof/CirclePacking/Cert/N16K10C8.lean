import C16Compute

/-! Computation: chunk 8 of 14 of the run `n = 16`, `k = 10` (search tree first expanded to depth 16).
Imports only the computational core. -/

namespace CirclePacking

theorem n16_k10_c8 : checkChunk (P16 10) (fun _ => false) 400 16 14 8 = true := by native_decide

end CirclePacking
