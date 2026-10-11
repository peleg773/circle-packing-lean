import CirclePacking.BnB
import CirclePacking.Cert.N18K8C0
import CirclePacking.Cert.N18K8C1
import CirclePacking.Cert.N18K8C2
import CirclePacking.Cert.N18K8C3
import CirclePacking.Cert.N18K8C4
import CirclePacking.Cert.N18K8C5
import CirclePacking.Cert.N18K8C6
import CirclePacking.Cert.N18K8C7
import CirclePacking.Cert.N18K8C8
import CirclePacking.Cert.N18K8C9
import CirclePacking.Cert.N18K8C10
import CirclePacking.Cert.N18K8C11
import CirclePacking.Cert.N18K8C12
import CirclePacking.Cert.N18K8C13
import CirclePacking.Cert.N18K8C14
import CirclePacking.Cert.N18K8C15

/-! The run `n = 18`, `k = 8` is certified (from its 16 chunks). -/

namespace CirclePacking

theorem n18_k8 : Certified (P18 8) (survRef18 8) := by
  apply certified_of_chunks (fuel := 400) (d := 16) (m := 16) (by norm_num)
  intro i hi
  interval_cases i
  exacts [n18_k8_c0, n18_k8_c1, n18_k8_c2, n18_k8_c3, n18_k8_c4, n18_k8_c5, n18_k8_c6, n18_k8_c7, n18_k8_c8, n18_k8_c9, n18_k8_c10, n18_k8_c11, n18_k8_c12, n18_k8_c13, n18_k8_c14, n18_k8_c15]

end CirclePacking
