import C18Compute

/-! Computation: chunk 17 of 128 of the run `n = 18`, `k = 11` (search tree first expanded to depth 16).
Imports only the computational core. -/

namespace CirclePacking

theorem n18_k11_c17 : checkChunk (P18 11) (fun _ => false) 400 16 128 17 = true := by native_decide

end CirclePacking
