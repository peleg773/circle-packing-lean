import C18Compute

/-! Computation: chunk 116 of 128 of the run `n = 18`, `k = 13` (search tree first expanded to depth 16).
Imports only the computational core. -/

namespace CirclePacking

theorem n18_k13_c116 : checkChunk (P18 13) (fun _ => false) 400 16 128 116 = true := by native_decide

end CirclePacking
