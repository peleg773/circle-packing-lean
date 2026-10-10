import CirclePacking.BnB
import CirclePacking.Cert.N16K11C0
import CirclePacking.Cert.N16K11C1
import CirclePacking.Cert.N16K11C2
import CirclePacking.Cert.N16K11C3
import CirclePacking.Cert.N16K11C4
import CirclePacking.Cert.N16K11C5
import CirclePacking.Cert.N16K11C6
import CirclePacking.Cert.N16K11C7
import CirclePacking.Cert.N16K11C8
import CirclePacking.Cert.N16K11C9
import CirclePacking.Cert.N16K11C10
import CirclePacking.Cert.N16K11C11
import CirclePacking.Cert.N16K11C12
import CirclePacking.Cert.N16K11C13
import CirclePacking.Cert.N16K11C14
import CirclePacking.Cert.N16K11C15
import CirclePacking.Cert.N16K11C16
import CirclePacking.Cert.N16K11C17
import CirclePacking.Cert.N16K11C18
import CirclePacking.Cert.N16K11C19
import CirclePacking.Cert.N16K11C20
import CirclePacking.Cert.N16K11C21
import CirclePacking.Cert.N16K11C22
import CirclePacking.Cert.N16K11C23

/-! The run `n = 16`, `k = 11` is certified (from its 24 chunks). -/

namespace CirclePacking

theorem n16_k11 : Certified (P16 11) (fun _ => false) := by
  apply certified_of_chunks (fuel := 400) (d := 16) (m := 24) (by norm_num)
  intro i hi
  interval_cases i
  exacts [n16_k11_c0, n16_k11_c1, n16_k11_c2, n16_k11_c3, n16_k11_c4, n16_k11_c5, n16_k11_c6, n16_k11_c7, n16_k11_c8, n16_k11_c9, n16_k11_c10, n16_k11_c11, n16_k11_c12, n16_k11_c13, n16_k11_c14, n16_k11_c15, n16_k11_c16, n16_k11_c17, n16_k11_c18, n16_k11_c19, n16_k11_c20, n16_k11_c21, n16_k11_c22, n16_k11_c23]

end CirclePacking
