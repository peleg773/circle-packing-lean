import C16Compute

/-! Computation: the runs `n = 16`, `k ∈ {0,…,4} ∪ {12,…,16}` (closed at the root). Imports only the
computational core. -/

namespace CirclePacking

def n16small : Bool :=
  [0, 1, 2, 3, 4, 12, 13, 14, 15, 16].all (fun k => checkRun (P16 k) (fun _ => false) 400)

theorem n16small_true : n16small = true := by native_decide

end CirclePacking
