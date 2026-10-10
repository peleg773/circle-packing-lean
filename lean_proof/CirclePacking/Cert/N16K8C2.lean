import C16Compute

/-! Computation: chunk 2 of 6 of the run `n = 16`, `k = 8` (search tree first expanded to depth 16).
Imports only the computational core. -/

namespace CirclePacking

theorem n16_k8_c2 : checkChunk (P16 8) (fun _ => false) 400 16 6 2 = true := by native_decide

end CirclePacking
