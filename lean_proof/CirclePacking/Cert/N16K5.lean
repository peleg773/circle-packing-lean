import CirclePacking.BnB
import CirclePacking.Cert.N16K5C0
import CirclePacking.Cert.N16K5C1

/-! The run `n = 16`, `k = 5` is certified (from its 2 chunks). -/

namespace CirclePacking

theorem n16_k5 : Certified (P16 5) (survOK16 (P16 5)) := by
  apply certified_of_chunks (fuel := 400) (d := 16) (m := 2) (by norm_num)
  intro i hi
  interval_cases i
  exacts [n16_k5_c0, n16_k5_c1]

end CirclePacking
