import CirclePacking.BnB
import CirclePacking.Cert.N16K9C0
import CirclePacking.Cert.N16K9C1
import CirclePacking.Cert.N16K9C2
import CirclePacking.Cert.N16K9C3
import CirclePacking.Cert.N16K9C4
import CirclePacking.Cert.N16K9C5
import CirclePacking.Cert.N16K9C6
import CirclePacking.Cert.N16K9C7
import CirclePacking.Cert.N16K9C8

/-! The run `n = 16`, `k = 9` is certified (from its 9 chunks). -/

namespace CirclePacking

theorem n16_k9 : Certified (P16 9) (fun _ => false) := by
  apply certified_of_chunks (fuel := 400) (d := 16) (m := 9) (by norm_num)
  intro i hi
  interval_cases i
  exacts [n16_k9_c0, n16_k9_c1, n16_k9_c2, n16_k9_c3, n16_k9_c4, n16_k9_c5, n16_k9_c6, n16_k9_c7, n16_k9_c8]

end CirclePacking
