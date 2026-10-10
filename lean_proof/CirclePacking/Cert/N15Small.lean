import C15Compute

/-! Computation: the runs `n = 15`, `k ∈ {0,…,4} ∪ {11,…,15}` (closed at the root). Imports only the
computational core. -/

namespace CirclePacking

def n15small : Bool :=
  [0, 1, 2, 3, 4, 11, 12, 13, 14, 15].all (fun k => checkRun (P15 k) (fun _ => false) 400)

theorem n15small_true : n15small = true := by native_decide

end CirclePacking
