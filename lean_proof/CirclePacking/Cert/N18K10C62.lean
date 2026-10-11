import C18Compute

/-! Computation: chunk 62 of 128 of the run `n = 18`, `k = 10` (search tree first expanded to depth 16).
Imports only the computational core. -/

namespace CirclePacking

theorem n18_k10_c62 : checkChunk (P18 10) (fun _ => false) 400 16 128 62 = true := by native_decide

end CirclePacking
