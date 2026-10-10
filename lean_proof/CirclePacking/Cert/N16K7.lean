import CirclePacking.BnB
import CirclePacking.Cert.N16K7C0
import CirclePacking.Cert.N16K7C1
import CirclePacking.Cert.N16K7C2

/-! The run `n = 16`, `k = 7` is certified (from its 3 chunks). -/

namespace CirclePacking

theorem n16_k7 : Certified (P16 7) (fun _ => false) := by
  apply certified_of_chunks (fuel := 400) (d := 16) (m := 3) (by norm_num)
  intro i hi
  interval_cases i
  exacts [n16_k7_c0, n16_k7_c1, n16_k7_c2]

end CirclePacking
