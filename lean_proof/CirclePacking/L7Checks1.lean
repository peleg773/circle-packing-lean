import CirclePacking.L7

/-! Kernel check of the KKT (equilibrium stress) identity of lemma L7. -/

namespace CirclePacking

set_option maxRecDepth 100000 in
theorem kktOK_true : kktOK = true := by decide +kernel

end CirclePacking
