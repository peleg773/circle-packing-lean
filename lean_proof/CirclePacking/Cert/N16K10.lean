import CirclePacking.BnB
import CirclePacking.Cert.N16K10C0
import CirclePacking.Cert.N16K10C1
import CirclePacking.Cert.N16K10C2
import CirclePacking.Cert.N16K10C3
import CirclePacking.Cert.N16K10C4
import CirclePacking.Cert.N16K10C5
import CirclePacking.Cert.N16K10C6
import CirclePacking.Cert.N16K10C7
import CirclePacking.Cert.N16K10C8
import CirclePacking.Cert.N16K10C9
import CirclePacking.Cert.N16K10C10
import CirclePacking.Cert.N16K10C11
import CirclePacking.Cert.N16K10C12
import CirclePacking.Cert.N16K10C13

/-! The run `n = 16`, `k = 10` is certified (from its 14 chunks). -/

namespace CirclePacking

theorem n16_k10 : Certified (P16 10) (fun _ => false) := by
  apply certified_of_chunks (fuel := 400) (d := 16) (m := 14) (by norm_num)
  intro i hi
  interval_cases i
  exacts [n16_k10_c0, n16_k10_c1, n16_k10_c2, n16_k10_c3, n16_k10_c4, n16_k10_c5, n16_k10_c6, n16_k10_c7, n16_k10_c8, n16_k10_c9, n16_k10_c10, n16_k10_c11, n16_k10_c12, n16_k10_c13]

end CirclePacking
