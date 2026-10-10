import CirclePacking.BnB
import CirclePacking.Cert.N15K5Run

/-! The run `n = 15`, `k = 5` is certified. -/

namespace CirclePacking

theorem n15_k5 : Certified (P15 5) (survOK (P15 5)) := certified_of_checkRun n15_k5_run

end CirclePacking
