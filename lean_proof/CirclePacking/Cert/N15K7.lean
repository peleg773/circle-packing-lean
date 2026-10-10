import CirclePacking.BnB
import CirclePacking.Cert.N15K7C0
import CirclePacking.Cert.N15K7C1
import CirclePacking.Cert.N15K7C2

/-! The run `n = 15`, `k = 7` is certified (from its 3 chunks). -/

namespace CirclePacking

theorem n15_k7 : Certified (P15 7) (fun _ => false) := by
  apply certified_of_chunks (fuel := 400) (d := 16) (m := 3) (by norm_num)
  intro i hi
  interval_cases i
  exacts [n15_k7_c0, n15_k7_c1, n15_k7_c2]

end CirclePacking
