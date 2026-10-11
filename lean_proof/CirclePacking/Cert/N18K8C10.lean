import C18Ref

/-! Computation: chunk 10 of 16 of the run `n = 18`, `k = 8` (search tree first expanded to depth 16).
Imports only the computational core. -/

namespace CirclePacking

theorem n18_k8_c10 : checkChunk (P18 8) (survRef18 8) 400 16 16 10 = true := by native_decide

end CirclePacking
