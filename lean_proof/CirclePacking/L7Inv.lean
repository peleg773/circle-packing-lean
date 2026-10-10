import CirclePacking.L7

/-! The left-inverse check of lemma L7, split by rows (each row is kernel-checked separately). -/

namespace CirclePacking

/-- row `i` of the left-inverse identity `M · L_free = I` -/
def invRow (i : ℕ) : Bool := (List.range 29).all fun j =>
  decide (sumQ 30 (fun r => Mi i r * Lm r (fcol j)) = if i = j then 1 else 0)

lemma invOK_of_rows (h : ∀ i < 29, invRow i = true) : invOK = true := by
  unfold invOK
  rw [List.all_eq_true]
  intro i hi
  exact h i (List.mem_range.mp hi)

end CirclePacking
