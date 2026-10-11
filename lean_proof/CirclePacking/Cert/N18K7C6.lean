import C18Ref

/-! Computation: chunk 6 of 8 of the run `n = 18`, `k = 7` (search tree first expanded to depth 16).
Imports only the computational core. -/

namespace CirclePacking

theorem n18_k7_c6 : checkChunk (P18 7) (survRef18 7) 400 16 8 6 = true := by native_decide

end CirclePacking
