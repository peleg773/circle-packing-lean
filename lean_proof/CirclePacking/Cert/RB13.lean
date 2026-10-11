import CirclePacking.BnB
import CirclePacking.Cert.RB13Run

/-! The radius-bound runs `m = 13` are certified. -/

namespace CirclePacking

theorem rb13_certs : ∀ k ≤ 13, Certified (Prb13 k) (fun _ => false) := by
  intro k hk
  have h := rb13All_true
  unfold rb13All at h
  simp only [List.all_eq_true, List.mem_range] at h
  exact certified_of_checkRun (h k (by omega))

end CirclePacking
