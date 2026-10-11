import C18Compute

/-! Computation: chunk 14 of 32 of the run `n = 18`, `k = 9` (search tree first expanded to depth 16).
Imports only the computational core. -/

namespace CirclePacking

theorem n18_k9_c14 : checkChunk (P18 9) (fun _ => false) 400 16 32 14 = true := by native_decide

end CirclePacking
