import CirclePacking.L7Inv

/-! Kernel check of rows 0–14 of the left inverse of lemma L7. -/

namespace CirclePacking

set_option maxRecDepth 100000 in
theorem invRow_0 : invRow 0 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem invRow_1 : invRow 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem invRow_2 : invRow 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem invRow_3 : invRow 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem invRow_4 : invRow 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem invRow_5 : invRow 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem invRow_6 : invRow 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem invRow_7 : invRow 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem invRow_8 : invRow 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem invRow_9 : invRow 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem invRow_10 : invRow 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem invRow_11 : invRow 11 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem invRow_12 : invRow 12 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem invRow_13 : invRow 13 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem invRow_14 : invRow 14 = true := by decide +kernel

end CirclePacking
