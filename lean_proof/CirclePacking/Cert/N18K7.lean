import CirclePacking.BnB
import CirclePacking.Cert.N18K7C0
import CirclePacking.Cert.N18K7C1
import CirclePacking.Cert.N18K7C2
import CirclePacking.Cert.N18K7C3
import CirclePacking.Cert.N18K7C4
import CirclePacking.Cert.N18K7C5
import CirclePacking.Cert.N18K7C6
import CirclePacking.Cert.N18K7C7

/-! The run `n = 18`, `k = 7` is certified (from its 8 chunks). -/

namespace CirclePacking

theorem n18_k7 : Certified (P18 7) (survRef18 7) := by
  apply certified_of_chunks (fuel := 400) (d := 16) (m := 8) (by norm_num)
  intro i hi
  interval_cases i
  exacts [n18_k7_c0, n18_k7_c1, n18_k7_c2, n18_k7_c3, n18_k7_c4, n18_k7_c5, n18_k7_c6, n18_k7_c7]

end CirclePacking
