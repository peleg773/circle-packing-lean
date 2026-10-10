import CirclePacking.BnB
import CirclePacking.Cert.N15K8C0
import CirclePacking.Cert.N15K8C1
import CirclePacking.Cert.N15K8C2
import CirclePacking.Cert.N15K8C3

/-! The run `n = 15`, `k = 8` is certified (from its 4 chunks). -/

namespace CirclePacking

theorem n15_k8 : Certified (P15 8) (fun _ => false) := by
  apply certified_of_chunks (fuel := 400) (d := 16) (m := 4) (by norm_num)
  intro i hi
  interval_cases i
  exacts [n15_k8_c0, n15_k8_c1, n15_k8_c2, n15_k8_c3]

end CirclePacking
