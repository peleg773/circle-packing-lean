import C15Compute

/-! Computation: chunk 4 of 5 of the run `n = 15`, `k = 9` (search tree first expanded to depth 16).
Imports only the computational core. -/

namespace CirclePacking

theorem n15_k9_c4 : checkChunk (P15 9) (fun _ => false) 400 16 5 4 = true := by native_decide

end CirclePacking
