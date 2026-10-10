import C16Compute

/-! Computation: chunk 18 of 24 of the run `n = 16`, `k = 11` (search tree first expanded to depth 16).
Imports only the computational core. -/

namespace CirclePacking

theorem n16_k11_c18 : checkChunk (P16 11) (fun _ => false) 400 16 24 18 = true := by native_decide

end CirclePacking
