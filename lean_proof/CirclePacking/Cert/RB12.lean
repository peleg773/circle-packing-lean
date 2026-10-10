import CirclePacking.BnB
import CirclePacking.Cert.RB12Run

/-! The radius-bound runs `m = 12` are certified. -/

namespace CirclePacking

theorem rb12_certs : ∀ k ≤ 12, Certified (Prb12 k) (fun _ => false) := by
  intro k hk
  have h := rb12All_true
  unfold rb12All at h
  simp only [List.all_eq_true, List.mem_range] at h
  exact certified_of_checkRun (h k (by omega))

end CirclePacking
