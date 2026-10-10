import CirclePacking.Radius
import CirclePacking.Cert.RBRun

/-! The radius-bound runs `m = 8, …, 11` are certified. -/

namespace CirclePacking

theorem rb_certs : ∀ m, 8 ≤ m → m ≤ 11 → ∀ k ≤ m, Certified (Prb m k) (fun _ => false) := by
  intro m h1 h2 k hk
  have h := rbAll_true
  unfold rbAll at h
  simp only [List.all_eq_true, List.mem_cons, List.mem_range, List.not_mem_nil, or_false] at h
  have hm : m = 8 ∨ m = 9 ∨ m = 10 ∨ m = 11 := by omega
  exact certified_of_checkRun (h m hm k (by omega))

end CirclePacking
