import CirclePacking.BnB
import CirclePacking.Cert.N16K8C0
import CirclePacking.Cert.N16K8C1
import CirclePacking.Cert.N16K8C2
import CirclePacking.Cert.N16K8C3
import CirclePacking.Cert.N16K8C4
import CirclePacking.Cert.N16K8C5

/-! The run `n = 16`, `k = 8` is certified (from its 6 chunks). -/

namespace CirclePacking

theorem n16_k8 : Certified (P16 8) (fun _ => false) := by
  apply certified_of_chunks (fuel := 400) (d := 16) (m := 6) (by norm_num)
  intro i hi
  interval_cases i
  exacts [n16_k8_c0, n16_k8_c1, n16_k8_c2, n16_k8_c3, n16_k8_c4, n16_k8_c5]

end CirclePacking
