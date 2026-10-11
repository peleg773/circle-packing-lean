import C18Ref

/-! Computation: chunk 5 of 8 of the run `n = 18`, `k = 7` (search tree first expanded to depth 16).
Imports only the computational core. -/

namespace CirclePacking

theorem n18_k7_c5 : checkChunk (P18 7) (survRef18 7) 400 16 8 5 = true := by native_decide

end CirclePacking
