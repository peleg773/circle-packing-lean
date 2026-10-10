import C15Compute

/-! Computation: chunk 2 of 3 of the run `n = 15`, `k = 7` (search tree first expanded to depth 16).
Imports only the computational core. -/

namespace CirclePacking

theorem n15_k7_c2 : checkChunk (P15 7) (fun _ => false) 400 16 3 2 = true := by native_decide

end CirclePacking
