import CirclePacking.BnB
import CirclePacking.Cert.N16K6Run

/-! The run `n = 16`, `k = 6` is certified. -/

namespace CirclePacking

theorem n16_k6 : Certified (P16 6) (fun _ => false) := certified_of_checkRun n16_k6_run

end CirclePacking
