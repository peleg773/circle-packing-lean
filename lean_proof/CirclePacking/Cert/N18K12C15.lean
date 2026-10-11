import C18Compute

/-! Computation: chunk 15 of 128 of the run `n = 18`, `k = 12` (search tree first expanded to depth 16).
Imports only the computational core. -/

namespace CirclePacking

theorem n18_k12_c15 : checkChunk (P18 12) (fun _ => false) 400 16 128 15 = true := by native_decide

end CirclePacking
