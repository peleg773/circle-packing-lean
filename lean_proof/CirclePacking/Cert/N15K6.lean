import CirclePacking.BnB
import CirclePacking.Cert.N15K6Run

/-! The run `n = 15`, `k = 6` is certified. -/

namespace CirclePacking

theorem n15_k6 : Certified (P15 6) (fun _ => false) := certified_of_checkRun n15_k6_run

end CirclePacking
