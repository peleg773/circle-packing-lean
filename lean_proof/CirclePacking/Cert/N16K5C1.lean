import C16Compute

/-! Computation: chunk 1 of 2 of the run `n = 16`, `k = 5` (search tree first expanded to depth 16).
Imports only the computational core. -/

namespace CirclePacking

theorem n16_k5_c1 : checkChunk (P16 5) (survOK16 (P16 5)) 400 16 2 1 = true := by native_decide

end CirclePacking
