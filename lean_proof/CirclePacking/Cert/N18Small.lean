import C18Compute

/-! Computation: the runs `n = 18`, `k ∈ {14,…,18}` (closed at the root). Imports only the computational
core. -/

namespace CirclePacking

def n18small : Bool :=
  [14, 15, 16, 17, 18].all (fun k => checkRun (P18 k) (fun _ => false) 400)

theorem n18small_true : n18small = true := by native_decide

end CirclePacking
