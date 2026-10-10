import C16Compute

/-! Computation: chunk 5 of 9 of the run `n = 16`, `k = 9` (search tree first expanded to depth 16).
Imports only the computational core. -/

namespace CirclePacking

theorem n16_k9_c5 : checkChunk (P16 9) (fun _ => false) 400 16 9 5 = true := by native_decide

end CirclePacking
