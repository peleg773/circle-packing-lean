import CirclePacking.BnB
import CirclePacking.Cert.RB14Run

/-! The radius-bound runs `m = 14` are certified. -/

namespace CirclePacking

theorem rb14_certs : ∀ k ≤ 14, Certified (Prb14 k) (fun _ => false) := by
  intro k hk
  have h := rb14All_true
  unfold rb14All at h
  simp only [List.all_eq_true, List.mem_range] at h
  exact certified_of_checkRun (h k (by omega))

end CirclePacking
