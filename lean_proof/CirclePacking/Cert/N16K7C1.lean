import C16Compute

/-! Computation: chunk 1 of 3 of the run `n = 16`, `k = 7` (search tree first expanded to depth 16).
Imports only the computational core. -/

namespace CirclePacking

theorem n16_k7_c1 : checkChunk (P16 7) (fun _ => false) 400 16 3 1 = true := by native_decide

end CirclePacking
