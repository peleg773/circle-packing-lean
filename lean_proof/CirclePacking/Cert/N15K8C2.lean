import C15Compute

/-! Computation: chunk 2 of 4 of the run `n = 15`, `k = 8` (search tree first expanded to depth 16).
Imports only the computational core. -/

namespace CirclePacking

theorem n15_k8_c2 : checkChunk (P15 8) (fun _ => false) 400 16 4 2 = true := by native_decide

end CirclePacking
