import CirclePacking.BnB
import CirclePacking.Cert.N15K10C0
import CirclePacking.Cert.N15K10C1
import CirclePacking.Cert.N15K10C2
import CirclePacking.Cert.N15K10C3
import CirclePacking.Cert.N15K10C4
import CirclePacking.Cert.N15K10C5
import CirclePacking.Cert.N15K10C6
import CirclePacking.Cert.N15K10C7

/-! The run `n = 15`, `k = 10` is certified (from its 8 chunks). -/

namespace CirclePacking

theorem n15_k10 : Certified (P15 10) (fun _ => false) := by
  apply certified_of_chunks (fuel := 400) (d := 16) (m := 8) (by norm_num)
  intro i hi
  interval_cases i
  exacts [n15_k10_c0, n15_k10_c1, n15_k10_c2, n15_k10_c3, n15_k10_c4, n15_k10_c5, n15_k10_c6, n15_k10_c7]

end CirclePacking
