import CirclePacking.Q23
import CirclePacking.Polar

/-!
# Points of the 19-circle lattice in polar form

`pointQ r a` is the point at radius `r` and angle `a · 15°`, computed exactly in `ℚ(√2, √3)` by `a` rotations
by `15°` (`cos 15° = (√6 + √2)/4`, `sin 15° = (√6 - √2)/4`).  `pointQ_eval`: it is `polar r (a / 24)`.
-/

open Real

namespace CirclePacking

/-- the radii `2`, `2√2`, `ρ₁₉ = √2 + √6` -/
def ringQ : Q23 := ⟨2, 0, 0, 0⟩
def s2Q : Q23 := ⟨0, 2, 0, 0⟩
def rho19Q : Q23 := ⟨0, 1, 0, 1⟩

/-- `cos 15°` and `sin 15°` in `ℚ(√2, √3)` -/
def c15Q : Q23 := ⟨0, 1 / 4, 0, 1 / 4⟩
def s15Q : Q23 := ⟨0, -1 / 4, 0, 1 / 4⟩

/-- rotation by `15°` -/
def rot15 (p : Q23 × Q23) : Q23 × Q23 := (p.1 * c15Q - p.2 * s15Q, p.1 * s15Q + p.2 * c15Q)

/-- the point at radius `r` and angle `a · 15°` -/
def pointQ (r : Q23) : ℕ → Q23 × Q23
  | 0 => (r, 0)
  | a + 1 => rot15 (pointQ r a)

lemma cos_pi_div_twelve : cos (π / 12) = (√2 + √2 * √3) / 4 := by
  have e : π / 12 = π / 4 - π / 6 := by ring
  rw [e, cos_sub, cos_pi_div_four, sin_pi_div_four, cos_pi_div_six, sin_pi_div_six]
  ring

lemma sin_pi_div_twelve : sin (π / 12) = (-√2 + √2 * √3) / 4 := by
  have e : π / 12 = π / 4 - π / 6 := by ring
  rw [e, sin_sub, cos_pi_div_four, sin_pi_div_four, cos_pi_div_six, sin_pi_div_six]
  ring

lemma c15Q_eval : c15Q.eval = cos (π / 12) := by
  rw [cos_pi_div_twelve]; simp [c15Q, Q23.eval]; ring

lemma s15Q_eval : s15Q.eval = sin (π / 12) := by
  rw [sin_pi_div_twelve]; simp [s15Q, Q23.eval]; ring

lemma polar_succ15 (r t : ℝ) : polar r (t + 1 / 24) =
    ⟨(polar r t).re * cos (π / 12) - (polar r t).im * sin (π / 12),
      (polar r t).re * sin (π / 12) + (polar r t).im * cos (π / 12)⟩ := by
  have e : 2 * π * (t + 1 / 24) = 2 * π * t + π / 12 := by ring
  apply Complex.ext <;> simp only [polar, e, cos_add, sin_add] <;> ring

/-- **The lattice points in polar form.** -/
theorem pointQ_eval (r : Q23) (a : ℕ) :
    (⟨(pointQ r a).1.eval, (pointQ r a).2.eval⟩ : ℂ) = polar r.eval (a / 24) := by
  induction a with
  | zero => simp [pointQ, polar, Q23.eval_zero]
  | succ a ih =>
    have e : ((a + 1 : ℕ) : ℝ) / 24 = (a : ℝ) / 24 + 1 / 24 := by push_cast; ring
    rw [e, polar_succ15, ← ih]
    simp only [pointQ, rot15, Q23.eval_sub, Q23.eval_add, Q23.eval_mul, c15Q_eval, s15Q_eval]

end CirclePacking
