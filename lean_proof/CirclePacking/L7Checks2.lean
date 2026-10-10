import CirclePacking.L7InvA
import CirclePacking.L7InvB

/-! The left-inverse identity of lemma L7. -/

namespace CirclePacking

theorem invOK_true : invOK = true := by
  apply invOK_of_rows
  intro i hi
  interval_cases i
  exacts [invRow_0, invRow_1, invRow_2, invRow_3, invRow_4, invRow_5, invRow_6, invRow_7, invRow_8, invRow_9, invRow_10, invRow_11, invRow_12, invRow_13, invRow_14, invRow_15, invRow_16, invRow_17, invRow_18, invRow_19, invRow_20, invRow_21, invRow_22, invRow_23, invRow_24, invRow_25, invRow_26, invRow_27, invRow_28]

end CirclePacking
