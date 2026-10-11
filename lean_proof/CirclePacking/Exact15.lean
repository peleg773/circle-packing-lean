import CirclePacking.CStar

/-!
# The 15-circle optimum, explicitly

`ρ*` in closed form (`ρs_closed`), and the optimal configuration `optimal15` given by closed formulas:
* an inner regular pentagon of side `2` (circumradius `1 / sin (π/5)`);
* ten outer centres on the circle of radius `ρ = √(6 + 2/√5 + 4√(1 + 2/√5))`, two touching each inner circle,
  at the angles `2πj/5 ± α` with `α = arccos ((ρ² + r² - 4) / (2ρr))`.

`optimal15_eq_Cs`: `optimal15` is the record configuration `c*` of `CirclePacking.CStar` (exact coordinates in
`ℚ(sin π/5)`).
-/

open Real

namespace CirclePacking

/-! ### `ρ*` in closed form -/

lemma sqrt5_eq : √5 = 5 - 8 * QK.s5 ^ 2 := by have := QK.s5_sq; linarith

lemma sqrt_cot : √(1 + 2 / √5) = (3 / 2 - 2 * QK.s5 ^ 2) / QK.s5 := by
  have hs := QK.s5_pos
  have hb := QK.s5_bounds
  have hp := QK.s5_poly
  have h5 : 0 < √5 := by positivity
  have hc : 0 < 3 / 2 - 2 * QK.s5 ^ 2 := by
    obtain ⟨-, hh⟩ := hb
    have : QK.s5 ^ 2 ≤ (QK.sHi : ℝ) ^ 2 := pow_le_pow_left₀ hs.le hh 2
    have hv : (QK.sHi : ℝ) ^ 2 < 3 / 4 := by unfold QK.sHi; norm_num
    linarith
  rw [Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)]
  rw [div_pow, eq_div_iff (by positivity)]
  rw [sqrt5_eq] at h5 ⊢
  field_simp
  linear_combination (8 * QK.s5 ^ 2 - 9) * hp

theorem ρs_closed : ρs = √(6 + 2 / √5 + 4 * √(1 + 2 / √5)) := by
  unfold ρs
  congr 1
  have hs := QK.s5_pos
  have hp := QK.s5_poly
  have h5 : 0 < √5 := by positivity
  rw [sqrt_cot]
  rw [sqrt5_eq] at h5 ⊢
  simp only [rho2K, QK.eval]
  push_cast
  field_simp
  linear_combination (96 * QK.s5 ^ 2 + 16 * QK.s5 - 60) * hp

/-! ### The explicit optimal configuration of 15 circles -/

namespace Opt15

/-- radius of the circle through the ten outer centres -/
noncomputable def ρ : ℝ := √(6 + 2 / √5 + 4 * √(1 + 2 / √5))

/-- radius of the circle through the five inner centres (a regular pentagon of side `2`) -/
noncomputable def r : ℝ := 1 / Real.sin (π / 5)

/-- the angle, seen from `0`, between an inner centre and each of the two outer centres touching it -/
noncomputable def α : ℝ := Real.arccos ((ρ ^ 2 + r ^ 2 - 4) / (2 * ρ * r))

/-- the point at distance `d` from `0` in the direction `θ` -/
noncomputable def P (d θ : ℝ) : ℂ := ⟨d * Real.cos θ, d * Real.sin θ⟩

end Opt15

open Opt15 in
/-- **The optimal configuration of 15 unit circles** (centres; container centred at `0`): an inner regular pentagon
of side `2` and ten outer centres on the circle of radius `ρ`, two touching each inner circle -/
noncomputable def optimal15 : Fin 15 → ℂ :=
  ![P r 0, P r (2 * π / 5), P r (4 * π / 5), P r (6 * π / 5), P r (8 * π / 5),
    P ρ α, P ρ (2 * π / 5 - α), P ρ (2 * π / 5 + α), P ρ (4 * π / 5 - α), P ρ (4 * π / 5 + α),
    P ρ (6 * π / 5 - α), P ρ (6 * π / 5 + α), P ρ (8 * π / 5 - α), P ρ (8 * π / 5 + α), P ρ (2 * π - α)]

lemma P_eq_polar (d θ : ℝ) : Opt15.P d θ = polar d (θ / (2 * π)) := by
  have : 2 * π * (θ / (2 * π)) = θ := by field_simp
  simp only [Opt15.P, polar, this]

lemma sin_pi_div_five_pos : 0 < Real.sin (π / 5) :=
  Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])

lemma r5_eq : r5 = Opt15.r := by
  have h : cx 0 * sK = 1 := by decide +kernel
  have h' := congrArg QK.eval h
  rw [QK.eval_mul, eval_sK, QK.eval_one] at h'
  have hs := sin_pi_div_five_pos
  unfold Opt15.r
  rw [eq_div_iff hs.ne']
  exact h'

lemma r5_pos : 0 < r5 := by rw [r5_eq]; unfold Opt15.r; exact one_div_pos.mpr sin_pi_div_five_pos

lemma ρs_eq : ρs = Opt15.ρ := ρs_closed

lemma two_pi_αs_eq : 2 * π * αs = Opt15.α := by
  rw [two_pi_αs, Opt15.α, ← ρs_eq, ← r5_eq]
  congr 1
  obtain ⟨-, -, -, hc⟩ := contactsOK_spec contactsOK_true (r := 2) (by norm_num)
  have e1 : ctc 2 = (0, 5) := rfl
  rw [e1] at hc
  simp only [QK.eval_sub] at hc
  have hy0 : (cy 0).eval = 0 := by rw [cy0, QK.eval_zero]
  rw [hy0] at hc
  have hb := norm_Cs5_sq
  have hs2 := ρs_sq
  have key : 2 * (cx 0).eval * (cx 5).eval = ρs ^ 2 + (cx 0).eval ^ 2 - 4 := by
    linear_combination -hc + hb - hs2
  have hρ := ρs_pos
  have hr := r5_pos
  rw [div_eq_div_iff hρ.ne' (by positivity)]
  simp only [r5]
  linear_combination ρs * key

lemma Cs6 : Cs 6 = (starRingEnd ℂ) (Cs 5) * ω5 := by
  rw [Cs_of_cst rot_q0]
  apply Complex.ext
  · simp only [rotK, QK.eval_sub, QK.eval_mul, QK.eval_neg, eval_c72K, eval_s72K, ω5, polar, Complex.mul_re,
      Complex.conj_re, Complex.conj_im, Cs, cx, cy]
    ring
  · simp only [rotK, QK.eval_add, QK.eval_mul, QK.eval_neg, eval_c72K, eval_s72K, ω5, polar, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Cs, cx, cy]
    ring

lemma conj_polar (d t : ℝ) : (starRingEnd ℂ) (polar d t) = polar d (-t) := by
  apply Complex.ext <;> simp [polar, Real.cos_neg, Real.sin_neg, mul_neg]

lemma polar_mul_ω5 (d t : ℝ) : polar d t * ω5 = polar d (t + 1 / 5) := by
  rw [ω5, polar_mul, mul_one]

lemma Cs_outer {j : ℕ} (hj : j < 5) :
    Cs (5 + 2 * j) = polar ρs (αs + j / 5) ∧ Cs (6 + 2 * j) = polar ρs ((j + 1) / 5 - αs) := by
  induction j with
  | zero =>
    refine ⟨by simpa using Cs5_polar, ?_⟩
    rw [show 6 + 2 * 0 = 6 from rfl, Cs6, Cs5_polar, conj_polar, polar_mul_ω5]
    congr 1; push_cast; ring
  | succ j ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    constructor
    · rw [show 5 + 2 * (j + 1) = 7 + 2 * j by ring, Cs_rot (rot_p (by omega)), h1, polar_mul_ω5]
      congr 1; push_cast; ring
    · rw [show 6 + 2 * (j + 1) = 8 + 2 * j by ring, Cs_rot (rot_q (by omega)), h2, polar_mul_ω5]
      congr 1; push_cast; ring

/-- **`optimal15` is the certified optimum `c*`.** -/
theorem optimal15_eq_Cs (i : Fin 15) : optimal15 i = Cs i := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have ha : Opt15.α / (2 * π) = αs := by rw [← two_pi_αs_eq]; field_simp
  have inner : ∀ j : ℕ, j < 5 → Opt15.P Opt15.r (2 * π * j / 5) = Cs j := by
    intro j hj
    rw [Cs_interior hj, P_eq_polar, r5_eq]
    congr 1
    field_simp
  have o1 : ∀ j : ℕ, j < 5 → Opt15.P Opt15.ρ (2 * π * j / 5 + Opt15.α) = Cs (5 + 2 * j) := by
    intro j hj
    rw [(Cs_outer hj).1, P_eq_polar, ρs_eq, ← ha]
    congr 1; field_simp; ring
  have o2 : ∀ j : ℕ, j < 5 → Opt15.P Opt15.ρ (2 * π * (j + 1) / 5 - Opt15.α) = Cs (6 + 2 * j) := by
    intro j hj
    rw [(Cs_outer hj).2, P_eq_polar, ρs_eq, ← ha]
    congr 1
    field_simp
  fin_cases i
  · have := inner 0 (by norm_num); push_cast at this; rw [← this]; simp [optimal15]
  · have := inner 1 (by norm_num); push_cast at this; rw [← this]; simp [optimal15]
  · have := inner 2 (by norm_num); push_cast at this; rw [← this]; simp [optimal15]; try ring_nf
  · have := inner 3 (by norm_num); push_cast at this; rw [← this]; simp [optimal15]; try ring_nf
  · have := inner 4 (by norm_num); push_cast at this; rw [← this]; simp [optimal15]; try ring_nf
  · have := o1 0 (by norm_num); push_cast at this; rw [← this]; simp [optimal15]
  · have := o2 0 (by norm_num); push_cast at this; rw [← this]; simp [optimal15]
  · have := o1 1 (by norm_num); push_cast at this; rw [← this]; simp [optimal15]; try ring_nf
  · have := o2 1 (by norm_num); push_cast at this; rw [← this]; simp [optimal15]; try ring_nf
  · have := o1 2 (by norm_num); push_cast at this; rw [← this]; simp [optimal15]; try ring_nf
  · have := o2 2 (by norm_num); push_cast at this; rw [← this]; simp [optimal15]; try ring_nf
  · have := o1 3 (by norm_num); push_cast at this; rw [← this]; simp [optimal15]; try ring_nf
  · have := o2 3 (by norm_num); push_cast at this; rw [← this]; simp [optimal15]; try ring_nf
  · have := o1 4 (by norm_num); push_cast at this; rw [← this]; simp [optimal15]; try ring_nf
  · have := o2 4 (by norm_num); push_cast at this; rw [← this]; simp [optimal15]; try ring_nf

end CirclePacking
