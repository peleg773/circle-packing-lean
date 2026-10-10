import C16Compute

/-! Computation: chunk 11 of 24 of the run `n = 16`, `k = 11` (search tree first expanded to depth 16).
Imports only the computational core. -/

namespace CirclePacking

theorem n16_k11_c11 : checkChunk (P16 11) (fun _ => false) 400 16 24 11 = true := by native_decide

end CirclePacking
