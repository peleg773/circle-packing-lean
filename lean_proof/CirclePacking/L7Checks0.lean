import CirclePacking.L7
namespace CirclePacking
set_option maxRecDepth 100000 in
theorem contactsOK_true : contactsOK = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem bndOK_true : bndOK = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gaugeOK_true : gaugeOK = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem multPosOK_true : multPosOK = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem weightOK_true : weightOK = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem boundOK_true : boundOK = true := by decide +kernel
end CirclePacking
