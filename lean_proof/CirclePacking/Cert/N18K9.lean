import CirclePacking.BnB
import CirclePacking.Cert.N18K9C0
import CirclePacking.Cert.N18K9C1
import CirclePacking.Cert.N18K9C2
import CirclePacking.Cert.N18K9C3
import CirclePacking.Cert.N18K9C4
import CirclePacking.Cert.N18K9C5
import CirclePacking.Cert.N18K9C6
import CirclePacking.Cert.N18K9C7
import CirclePacking.Cert.N18K9C8
import CirclePacking.Cert.N18K9C9
import CirclePacking.Cert.N18K9C10
import CirclePacking.Cert.N18K9C11
import CirclePacking.Cert.N18K9C12
import CirclePacking.Cert.N18K9C13
import CirclePacking.Cert.N18K9C14
import CirclePacking.Cert.N18K9C15
import CirclePacking.Cert.N18K9C16
import CirclePacking.Cert.N18K9C17
import CirclePacking.Cert.N18K9C18
import CirclePacking.Cert.N18K9C19
import CirclePacking.Cert.N18K9C20
import CirclePacking.Cert.N18K9C21
import CirclePacking.Cert.N18K9C22
import CirclePacking.Cert.N18K9C23
import CirclePacking.Cert.N18K9C24
import CirclePacking.Cert.N18K9C25
import CirclePacking.Cert.N18K9C26
import CirclePacking.Cert.N18K9C27
import CirclePacking.Cert.N18K9C28
import CirclePacking.Cert.N18K9C29
import CirclePacking.Cert.N18K9C30
import CirclePacking.Cert.N18K9C31

/-! The run `n = 18`, `k = 9` is certified (from its 32 chunks). -/

namespace CirclePacking

theorem n18_k9 : Certified (P18 9) (fun _ => false) := by
  apply certified_of_chunks (fuel := 400) (d := 16) (m := 32) (by norm_num)
  intro i hi
  interval_cases i
  exacts [n18_k9_c0, n18_k9_c1, n18_k9_c2, n18_k9_c3, n18_k9_c4, n18_k9_c5, n18_k9_c6, n18_k9_c7, n18_k9_c8, n18_k9_c9, n18_k9_c10, n18_k9_c11, n18_k9_c12, n18_k9_c13, n18_k9_c14, n18_k9_c15, n18_k9_c16, n18_k9_c17, n18_k9_c18, n18_k9_c19, n18_k9_c20, n18_k9_c21, n18_k9_c22, n18_k9_c23, n18_k9_c24, n18_k9_c25, n18_k9_c26, n18_k9_c27, n18_k9_c28, n18_k9_c29, n18_k9_c30, n18_k9_c31]

end CirclePacking
