import C18Compute

/-! Computation: chunk 17 of 32 of the run `n = 18`, `k = 9` (search tree first expanded to depth 16).
Imports only the computational core. -/

namespace CirclePacking

theorem n18_k9_c17 : checkChunk (P18 9) (fun _ => false) 400 16 32 17 = true := by native_decide

end CirclePacking
