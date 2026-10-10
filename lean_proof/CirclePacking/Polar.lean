import Mathlib

/-!
# Polar coordinates (angles in turns), the law of cosines, push-out
-/

open Real

namespace CirclePacking

/-- The point with polar coordinates `(r, 2π t)`; `t` is measured in turns. -/
noncomputable def polar (r t : ℝ) : ℂ := ⟨r * Real.cos (2 * π * t), r * Real.sin (2 * π * t)⟩

lemma normSq_polar_sub (r1 t1 r2 t2 : ℝ) :
    ‖polar r1 t1 - polar r2 t2‖ ^ 2 = r1 ^ 2 + r2 ^ 2 - 2 * r1 * r2 * Real.cos (2 * π * (t1 - t2)) := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [polar, Complex.sub_re, Complex.sub_im]
  have e : 2 * π * (t1 - t2) = 2 * π * t1 - 2 * π * t2 := by ring
  rw [e, Real.cos_sub]
  have h1 := Real.sin_sq_add_cos_sq (2 * π * t1)
  have h2 := Real.sin_sq_add_cos_sq (2 * π * t2)
  nlinarith [h1, h2]

lemma norm_polar {r : ℝ} (hr : 0 ≤ r) (t : ℝ) : ‖polar r t‖ = r := by
  have h := normSq_polar_sub r t 0 t
  have e : polar 0 t = 0 := by simp [polar]; rfl
  rw [e, sub_zero] at h
  simp at h
  have : ‖polar r t‖ ^ 2 = r ^ 2 := by rw [h]
  have hn := norm_nonneg (polar r t)
  nlinarith [sq_nonneg (‖polar r t‖ - r), sq_nonneg (‖polar r t‖ + r)]

lemma polar_add_int (r t : ℝ) (m : ℤ) : polar r (t + m) = polar r t := by
  simp only [polar]
  have e : 2 * π * (t + m) = 2 * π * t + (m : ℝ) * (2 * π) := by ring
  rw [e, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

/-- every point of the plane in polar form -/
lemma polar_norm_arg (z : ℂ) : polar ‖z‖ (Complex.arg z / (2 * π)) = z := by
  have hπ : (2 * π) ≠ 0 := by positivity
  have e : 2 * π * (Complex.arg z / (2 * π)) = Complex.arg z := by field_simp
  apply Complex.ext
  · simp only [polar, e]; exact Complex.norm_mul_cos_arg z
  · simp only [polar, e]; exact Complex.norm_mul_sin_arg z

/-- Strict decrease of `cos (2π ·)` translated to "circular distance": if `|x - m| < t ≤ 1/2` for some
integer `m`, then `cos (2π t) < cos (2π x)`. -/
lemma cos_turn_lt {x t : ℝ} {m : ℤ} (ht : t ≤ 1 / 2) (h : |x - m| < t) :
    Real.cos (2 * π * t) < Real.cos (2 * π * x) := by
  have e1 : Real.cos (2 * π * x) = Real.cos (2 * π * |x - m|) := by
    have h2 : 2 * π * |x - m| = |2 * π * (x - m)| := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
    rw [h2, Real.cos_abs]
    have : 2 * π * (x - m) = 2 * π * x + (-m : ℤ) * (2 * π) := by push_cast; ring
    rw [this, Real.cos_add_int_mul_two_pi]
  rw [e1]
  apply Real.cos_lt_cos_of_nonneg_of_le_pi
  · positivity
  · nlinarith [Real.pi_pos]
  · nlinarith [Real.pi_pos]

/-- contrapositive form: `cos (2π x) ≤ cos (2π t)` with `0 ≤ t ≤ 1/2` gives circular distance `≥ t`. -/
lemma le_abs_sub_int_of_cos_le {x t : ℝ} (ht : t ≤ 1 / 2)
    (h : Real.cos (2 * π * x) ≤ Real.cos (2 * π * t)) (m : ℤ) : t ≤ |x - m| := by
  by_contra hc
  push Not at hc
  exact absurd h (not_le.mpr (cos_turn_lt ht hc))

/-- **Push-out lemma** (one pair).  Moving `p` radially out to radius `ρ` keeps its distance `≥ 2` to
any `q` with `‖q‖ ≤ ρ`, provided `‖p‖² > ρ² - 4`. -/
lemma pushout_pair {p q : ℂ} {ρ : ℝ} (hp : ρ ^ 2 - 4 < ‖p‖ ^ 2) (hpρ : ‖p‖ ≤ ρ) (hq : ‖q‖ ≤ ρ)
    (hpq : 2 ≤ ‖p - q‖) : 2 ≤ ‖((ρ / ‖p‖ : ℝ) : ℂ) * p - q‖ := by
  have ha : 0 < ‖p‖ := by
    rcases (norm_nonneg p).lt_or_eq with h | h
    · exact h
    · exfalso
      have hp0 : p = 0 := norm_eq_zero.mp h.symm
      rw [hp0, zero_sub, norm_neg] at hpq
      have hρ2 : ρ < 2 := by
        rw [← h] at hp
        nlinarith [norm_nonneg q]
      linarith
  set a := ‖p‖ with ha_def
  have hρ : 0 < ρ := lt_of_lt_of_le ha hpρ
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  have hna : a ^ 2 = p1 ^ 2 + p2 ^ 2 := by
    rw [ha_def, Complex.sq_norm, Complex.normSq_apply]; ring
  have hnq : ‖(⟨q1, q2⟩ : ℂ)‖ ^ 2 = q1 ^ 2 + q2 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hpq2 : 4 ≤ (p1 - q1) ^ 2 + (p2 - q2) ^ 2 := by
    have h4 : (2 : ℝ) ^ 2 ≤ ‖(⟨p1, p2⟩ : ℂ) - ⟨q1, q2⟩‖ ^ 2 := by gcongr
    rw [Complex.sq_norm, Complex.normSq_apply] at h4
    simp at h4; nlinarith [h4]
  have hq2 : q1 ^ 2 + q2 ^ 2 ≤ ρ ^ 2 := by
    rw [← hnq]; gcongr
  suffices h : (2 : ℝ) ^ 2 ≤ ‖((ρ / a : ℝ) : ℂ) * ⟨p1, p2⟩ - ⟨q1, q2⟩‖ ^ 2 by
    exact le_of_pow_le_pow_left₀ (by norm_num) (norm_nonneg _) h
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_im, Complex.mul_im, zero_mul, sub_zero, add_zero]
  set l := ρ / a with hl
  have hla : l * a = ρ := by rw [hl]; field_simp
  have hF : (l * p1 - q1) * (l * p1 - q1) + (l * p2 - q2) * (l * p2 - q2)
      = ρ ^ 2 - 2 * l * (p1 * q1 + p2 * q2) + (q1 ^ 2 + q2 ^ 2) := by
    have : l ^ 2 * (p1 ^ 2 + p2 ^ 2) = ρ ^ 2 := by rw [← hna, ← hla]; ring
    nlinarith [this]
  rw [hF]
  -- a * (F - 4) - ρ * (f - 4) = (ρ - a) * (a ρ - r2 + 4)
  have key : a * (ρ ^ 2 - 2 * l * (p1 * q1 + p2 * q2) + (q1 ^ 2 + q2 ^ 2) - 4)
      = ρ * ((p1 - q1) ^ 2 + (p2 - q2) ^ 2 - 4) + (ρ - a) * (a * ρ - (q1 ^ 2 + q2 ^ 2) + 4) := by
    have e2 : a * (2 * l * (p1 * q1 + p2 * q2)) = 2 * ρ * (p1 * q1 + p2 * q2) := by
      rw [← hla]; ring
    nlinarith [e2, hna]
  have hpos : 0 ≤ (ρ - a) * (a * ρ - (q1 ^ 2 + q2 ^ 2) + 4) := by
    apply mul_nonneg (by linarith)
    nlinarith
  have h2 : 0 ≤ a * (ρ ^ 2 - 2 * l * (p1 * q1 + p2 * q2) + (q1 ^ 2 + q2 ^ 2) - 4) := by
    rw [key]; nlinarith
  have h3 : 0 ≤ ρ ^ 2 - 2 * l * (p1 * q1 + p2 * q2) + (q1 ^ 2 + q2 ^ 2) - 4 := by
    by_contra hc
    push Not at hc
    have := mul_neg_of_pos_of_neg ha hc
    linarith
  linarith

end CirclePacking
