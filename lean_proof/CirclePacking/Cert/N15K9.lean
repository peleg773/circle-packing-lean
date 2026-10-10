import CirclePacking.BnB
import CirclePacking.Cert.N15K9C0
import CirclePacking.Cert.N15K9C1
import CirclePacking.Cert.N15K9C2
import CirclePacking.Cert.N15K9C3
import CirclePacking.Cert.N15K9C4

/-! The run `n = 15`, `k = 9` is certified (from its 5 chunks). -/

namespace CirclePacking

theorem n15_k9 : Certified (P15 9) (fun _ => false) := by
  apply certified_of_chunks (fuel := 400) (d := 16) (m := 5) (by norm_num)
  intro i hi
  interval_cases i
  exacts [n15_k9_c0, n15_k9_c1, n15_k9_c2, n15_k9_c3, n15_k9_c4]

end CirclePacking
