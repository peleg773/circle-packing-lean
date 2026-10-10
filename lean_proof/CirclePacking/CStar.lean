import CirclePacking.L7Checks0
import CirclePacking.Canon

/-!
# The record configuration `c*` in polar form

`c*` (exact coordinates in `K = ℚ(sin π/5)`, module `L7Data`) has the inner pentagon
`v_j = r5 e^{2πi j/5}` and the boundary points `p_j = ρ* e^{2πi (j/5 + α)}`, `q_j = ρ* e^{2πi ((j+1)/5 - α)}`.
We prove these polar forms and certified brackets for `r5`, `ρ*²` and `α`.
-/

open Real

namespace CirclePacking

/-- point `p` of `c*` as a complex number -/
noncomputable def Cs (p : ℕ) : ℂ := ⟨(cx p).eval, (cy p).eval⟩

/-- the container radius `ρ*` of `c*` -/
noncomputable def ρs : ℝ := √(rho2K.eval)

/-- the radius of the inner pentagon, `1 / sin (π/5)` -/
noncomputable def r5 : ℝ := (cx 0).eval

/-- the angle (in turns) of the boundary point `p_0` -/
noncomputable def αs : ℝ := Real.arccos ((cx 5).eval / ρs) / (2 * π)

/-! ### Exact identities in `K` -/

def sK : QK := ⟨0, 1, 0, 0⟩
def c36K : QK := ⟨3 / 2, 0, -2, 0⟩
def c72K : QK := c36K * c36K - sK * sK
def s72K : QK := 2 * sK * c36K
/-- rotation by `72°` -/
def rotK (p : QK × QK) : QK × QK := (p.1 * c72K - p.2 * s72K, p.1 * s72K + p.2 * c72K)

def rotChecks : Bool := (List.range 4).all (fun j =>
  decide (cst (j + 1) = rotK (cst j)) && decide (cst (7 + 2 * j) = rotK (cst (5 + 2 * j))) &&
  decide (cst (8 + 2 * j) = rotK (cst (6 + 2 * j)))) &&
  decide (cst 6 = rotK ((cst 5).1, -(cst 5).2)) && decide (cy 0 = 0)

set_option maxRecDepth 100000 in
theorem rotChecks_true : rotChecks = true := by decide +kernel

lemma rot_int {j : ℕ} (hj : j < 4) : cst (j + 1) = rotK (cst j) := by
  have h := rotChecks_true
  unfold rotChecks at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact (h.1.1 j hj).1.1

lemma rot_p {j : ℕ} (hj : j < 4) : cst (7 + 2 * j) = rotK (cst (5 + 2 * j)) := by
  have h := rotChecks_true
  unfold rotChecks at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact (h.1.1 j hj).1.2

lemma rot_q {j : ℕ} (hj : j < 4) : cst (8 + 2 * j) = rotK (cst (6 + 2 * j)) := by
  have h := rotChecks_true
  unfold rotChecks at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact (h.1.1 j hj).2

lemma rot_q0 : cst 6 = rotK ((cst 5).1, -(cst 5).2) := by
  have h := rotChecks_true
  unfold rotChecks at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h.1.2

lemma cy0 : cy 0 = 0 := by
  have h := rotChecks_true
  unfold rotChecks at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h.2

/-! ### Evaluation of the rotation -/

lemma eval_sK : sK.eval = QK.s5 := by simp [sK, QK.eval]

lemma eval_c36K : c36K.eval = Real.cos (π / 5) := by
  rw [Real.cos_pi_div_five]
  have h := QK.s5_sq
  simp only [c36K, QK.eval]
  push_cast
  linarith

lemma eval_c72K : c72K.eval = Real.cos (2 * π * (1 / 5)) := by
  have e : 2 * π * (1 / 5) = 2 * (π / 5) := by ring
  rw [e, Real.cos_two_mul]
  simp only [c72K, QK.eval_sub, QK.eval_mul, eval_c36K, eval_sK]
  have h := Real.sin_sq_add_cos_sq (π / 5)
  unfold QK.s5
  nlinarith [h]

lemma eval_s72K : s72K.eval = Real.sin (2 * π * (1 / 5)) := by
  have e : 2 * π * (1 / 5) = 2 * (π / 5) := by ring
  rw [e, Real.sin_two_mul]
  simp only [s72K, QK.eval_mul, eval_c36K, eval_sK]
  rw [show (2 : QK).eval = 2 by show (QK.ofQ 2).eval = 2; simp]
  unfold QK.s5; ring

/-! ### Polar forms -/

lemma polar_mul (r t r' t' : ℝ) : polar r t * polar r' t' = polar (r * r') (t + t') := by
  apply Complex.ext <;>
    simp only [polar, Complex.mul_re, Complex.mul_im, mul_add, Real.cos_add, Real.sin_add] <;> ring

/-- the rotation by one fifth of a turn -/
noncomputable def ω5 : ℂ := polar 1 (1 / 5)

lemma Cs_of_cst {p : ℕ} {u : QK × QK} (h : cst p = u) : Cs p = ⟨u.1.eval, u.2.eval⟩ := by
  simp [Cs, cx, cy, h]

lemma Cs_rot {p q : ℕ} (h : cst q = rotK (cst p)) : Cs q = Cs p * ω5 := by
  rw [Cs_of_cst h]
  apply Complex.ext
  · simp only [rotK, QK.eval_sub, QK.eval_mul, eval_c72K, eval_s72K, ω5, polar, Complex.mul_re, Cs, cx, cy]
    ring
  · simp only [rotK, QK.eval_add, QK.eval_mul, eval_c72K, eval_s72K, ω5, polar, Complex.mul_im, Cs, cx, cy]
    ring

lemma Cs_interior {j : ℕ} (hj : j < 5) : Cs j = polar r5 (j / 5) := by
  induction j with
  | zero =>
    apply Complex.ext
    · simp [Cs, polar, r5]
    · simp [Cs, polar, cy0]
  | succ j ih =>
    rw [Cs_rot (rot_int (by omega)), ih (by omega), ω5, polar_mul, mul_one]
    congr 1
    push_cast; ring

lemma norm_Cs5_sq : (cx 5).eval ^ 2 + (cy 5).eval ^ 2 = rho2K.eval := by
  have h := (bndOK_spec bndOK_true (show 0 < 10 by norm_num)).2
  have e : bdi 0 = 5 := by decide
  rwa [e] at h

/-! ### Rational interval checks -/

lemma rho2_pos : 0 < rho2K.eval := by
  have h := QK.lo_le_eval rho2K
  have : (0 : ℚ) < QK.lo rho2K := by decide +kernel
  have : (0 : ℝ) < (QK.lo rho2K : ℝ) := by exact_mod_cast this
  linarith

lemma ρs_pos : 0 < ρs := Real.sqrt_pos.mpr rho2_pos

lemma ρs_sq : ρs ^ 2 = rho2K.eval := Real.sq_sqrt rho2_pos.le

lemma x5_pos : 0 < (cx 5).eval := by
  have h := QK.lo_le_eval (cx 5)
  have : (0 : ℚ) < QK.lo (cx 5) := by decide +kernel
  have : (0 : ℝ) < (QK.lo (cx 5) : ℝ) := by exact_mod_cast this
  linarith

lemma y5_pos : 0 < (cy 5).eval := by
  have h := QK.lo_le_eval (cy 5)
  have : (0 : ℚ) < QK.lo (cy 5) := by decide +kernel
  have : (0 : ℝ) < (QK.lo (cy 5) : ℝ) := by exact_mod_cast this
  linarith

lemma r5_bounds : sc r5Lo ≤ r5 ∧ r5 ≤ sc r5Hi := by
  have h1 := QK.lo_le_eval (cx 0)
  have h2 := QK.eval_le_hi (cx 0)
  have c1 : ((r5Lo : ℚ) / (S : ℚ)) ≤ QK.lo (cx 0) := by decide +kernel
  have c2 : QK.hi (cx 0) ≤ ((r5Hi : ℚ) / (S : ℚ)) := by decide +kernel
  have c1' : ((r5Lo : ℝ) / (S : ℝ)) ≤ (QK.lo (cx 0) : ℝ) := by exact_mod_cast c1
  have c2' : (QK.hi (cx 0) : ℝ) ≤ ((r5Hi : ℝ) / (S : ℝ)) := by exact_mod_cast c2
  unfold sc r5
  exact ⟨by linarith, by linarith⟩

lemma rho2_le : ρs ^ 2 ≤ (rho2Hi : ℝ) / ((S : ℝ) * S) := by
  rw [ρs_sq]
  have h := QK.eval_le_hi rho2K
  have c : QK.hi rho2K ≤ ((rho2Hi : ℚ) / ((S : ℚ) * S)) := by decide +kernel
  have c' : (QK.hi rho2K : ℝ) ≤ ((rho2Hi : ℝ) / ((S : ℝ) * S)) := by exact_mod_cast c
  linarith

/-! ### The angle `α` -/

lemma x5_le_ρs : (cx 5).eval ≤ ρs := by
  have h := norm_Cs5_sq
  have hy := y5_pos
  have hρ := ρs_pos
  rw [← ρs_sq] at h
  nlinarith

lemma cos_αs : Real.cos (2 * π * αs) = (cx 5).eval / ρs := by
  have e : 2 * π * αs = Real.arccos ((cx 5).eval / ρs) := by
    unfold αs; field_simp
  rw [e]
  have hρ := ρs_pos
  apply Real.cos_arccos
  · rw [le_div_iff₀ hρ]; nlinarith [x5_pos]
  · rw [div_le_one hρ]; exact x5_le_ρs

lemma sin_αs : Real.sin (2 * π * αs) = (cy 5).eval / ρs := by
  have e : 2 * π * αs = Real.arccos ((cx 5).eval / ρs) := by
    unfold αs; field_simp
  rw [e, Real.sin_arccos]
  have hρ := ρs_pos
  have h := norm_Cs5_sq
  rw [← ρs_sq] at h
  have e2 : 1 - ((cx 5).eval / ρs) ^ 2 = ((cy 5).eval / ρs) ^ 2 := by
    field_simp; linarith
  rw [e2, Real.sqrt_sq (div_nonneg y5_pos.le hρ.le)]

lemma Cs5_polar : Cs 5 = polar ρs αs := by
  have hρ := ρs_pos
  apply Complex.ext
  · simp only [Cs, polar, cos_αs]; field_simp
  · simp only [Cs, polar, sin_αs]; field_simp

lemma two_pi_αs : 2 * π * αs = Real.arccos ((cx 5).eval / ρs) := by
  unfold αs; field_simp

lemma αs_ge : sc alphaLo ≤ αs := by
  have hc : ((cx 5 * cx 5).hi : ℚ) * ((S : ℚ) * S) ≤
      ((cosZ alphaLo : ℚ) * cosZ alphaLo) * QK.lo rho2K := by decide +kernel
  have hpos : (0 : ℤ) ≤ cosZ alphaLo := by decide +kernel
  have hc' : ((cx 5 * cx 5).hi : ℝ) * ((S : ℝ) * S) ≤
      ((cosZ alphaLo : ℝ) * cosZ alphaLo) * (QK.lo rho2K : ℝ) := by exact_mod_cast hc
  have h1 := QK.eval_le_hi (cx 5 * cx 5)
  have h2 := QK.lo_le_eval rho2K
  rw [QK.eval_mul] at h1
  have hS : (0 : ℝ) < S := by exact_mod_cast S_pos
  have hcz : (0 : ℝ) ≤ cosZ alphaLo := by exact_mod_cast hpos
  have hρ := ρs_pos
  have hx := x5_pos
  have key : (cx 5).eval * S ≤ cosZ alphaLo * ρs := by
    have hsq : ((cx 5).eval * S) ^ 2 ≤ (cosZ alphaLo * ρs) ^ 2 := by
      rw [mul_pow, mul_pow, ρs_sq]
      have := mul_le_mul_of_nonneg_left h2 (mul_self_nonneg (cosZ alphaLo : ℝ))
      have hSS : 0 ≤ (S : ℝ) * S := mul_nonneg hS.le hS.le
      nlinarith [mul_le_mul_of_nonneg_right h1 hSS]
    exact le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg hcz hρ.le) hsq
  have h0 : (0 : ℤ) ≤ alphaLo := by decide
  have h12 : 2 * alphaLo ≤ S := by decide
  have hcos := cosZ_sc h0 h12
  have hle : (cx 5).eval / ρs ≤ Real.cos (2 * π * sc alphaLo) := by
    have : (cx 5).eval / ρs ≤ sc (cosZ alphaLo) := by
      unfold sc; rw [div_le_div_iff₀ hρ hS]; linarith
    linarith
  have hA := Real.arccos_le_arccos hle
  have hlo : 0 ≤ 2 * π * sc alphaLo := mul_nonneg (by positivity) (sc_nonneg h0)
  have hhi : 2 * π * sc alphaLo ≤ π := by
    have := half_of_two_le h12; nlinarith [Real.pi_pos]
  rw [Real.arccos_cos hlo hhi, ← two_pi_αs] at hA
  nlinarith [Real.pi_pos]

lemma αs_le : αs ≤ sc alphaHi := by
  have hc : (((-cosZ (S / 2 - alphaHi)) : ℚ) * (-cosZ (S / 2 - alphaHi))) * QK.hi rho2K ≤
      ((cx 5 * cx 5).lo : ℚ) * ((S : ℚ) * S) := by decide +kernel
  have hpos : (0 : ℤ) ≤ -cosZ (S / 2 - alphaHi) := by decide +kernel
  have hc' : (((-cosZ (S / 2 - alphaHi) : ℤ) : ℝ) * ((-cosZ (S / 2 - alphaHi) : ℤ) : ℝ)) * (QK.hi rho2K : ℝ) ≤
      ((cx 5 * cx 5).lo : ℝ) * ((S : ℝ) * S) := by exact_mod_cast hc
  have h1 := QK.lo_le_eval (cx 5 * cx 5)
  have h2 := QK.eval_le_hi rho2K
  rw [QK.eval_mul] at h1
  have hS : (0 : ℝ) < S := by exact_mod_cast S_pos
  have hcz : (0 : ℝ) ≤ ((-cosZ (S / 2 - alphaHi) : ℤ) : ℝ) := by exact_mod_cast hpos
  have hρ := ρs_pos
  have hx := x5_pos
  set c : ℝ := ((-cosZ (S / 2 - alphaHi) : ℤ) : ℝ) with hcdef
  have key : c * ρs ≤ (cx 5).eval * S := by
    have hsq : (c * ρs) ^ 2 ≤ ((cx 5).eval * S) ^ 2 := by
      rw [mul_pow, mul_pow, ρs_sq]
      have := mul_le_mul_of_nonneg_left h2 (mul_self_nonneg c)
      have hSS : 0 ≤ (S : ℝ) * S := mul_nonneg hS.le hS.le
      nlinarith [mul_le_mul_of_nonneg_right h1 hSS]
    exact le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg hx.le hS.le) hsq
  have h0 : (0 : ℤ) ≤ S / 2 - alphaHi := by decide
  have h12 : 2 * (S / 2 - alphaHi) ≤ S := by decide
  have hcos := cosZ_sc h0 h12
  have e : Real.cos (2 * π * sc (S / 2 - alphaHi)) = -Real.cos (2 * π * sc alphaHi) := by
    have : sc (S / 2 - alphaHi) = 1 / 2 - sc alphaHi := by
      rw [sc_sub]
      have : sc (S / 2) = 1 / 2 := by
        unfold sc
        have : ((S / 2 : ℤ) : ℝ) = (S : ℝ) / 2 := by
          have : S / 2 * 2 = S := by decide
          have h' : ((S / 2 : ℤ) : ℝ) * 2 = (S : ℝ) := by exact_mod_cast this
          linarith
        rw [this]; field_simp
      rw [this]
    rw [this, show 2 * π * (1 / 2 - sc alphaHi) = π - 2 * π * sc alphaHi by ring, Real.cos_pi_sub]
  have hle : Real.cos (2 * π * sc alphaHi) ≤ (cx 5).eval / ρs := by
    have : c / S ≤ (cx 5).eval / ρs := by
      rw [div_le_div_iff₀ hS hρ]; linarith
    have hc2 : sc (cosZ (S / 2 - alphaHi)) = -(c / S) := by
      rw [hcdef]; unfold sc; push_cast; ring
    linarith
  have hA := Real.arccos_le_arccos hle
  have h0' : (0 : ℤ) ≤ alphaHi := by decide
  have h12' : 2 * alphaHi ≤ S := by decide
  have hlo : 0 ≤ 2 * π * sc alphaHi := mul_nonneg (by positivity) (sc_nonneg h0')
  have hhi : 2 * π * sc alphaHi ≤ π := by
    have := half_of_two_le h12'; nlinarith [Real.pi_pos]
  rw [Real.arccos_cos hlo hhi, ← two_pi_αs] at hA
  nlinarith [Real.pi_pos]

/-! ### Polar forms of the boundary points -/

lemma Cs_p {j : ℕ} (hj : j < 5) : Cs (5 + 2 * j) = polar ρs (αs + j / 5) := by
  induction j with
  | zero => simp [Cs5_polar]
  | succ j ih =>
    rw [show 5 + 2 * (j + 1) = 7 + 2 * j by ring, Cs_rot (rot_p (by omega)), ih (by omega), ω5, polar_mul,
      mul_one]
    congr 1
    push_cast; ring

lemma Cs6_polar : Cs 6 = polar ρs (1 / 5 - αs) := by
  rw [Cs_of_cst rot_q0]
  have e : polar ρs (1 / 5 - αs) = polar ρs (-αs) * ω5 := by
    rw [ω5, polar_mul, mul_one]; congr 1; ring
  rw [e]
  have hc : polar ρs (-αs) = ⟨(cx 5).eval, -(cy 5).eval⟩ := by
    rw [polar_neg_angle, ← Cs5_polar]; rfl
  rw [hc]
  apply Complex.ext
  · simp only [rotK, QK.eval_sub, QK.eval_mul, QK.eval_neg, eval_c72K, eval_s72K, ω5, polar, Complex.mul_re, cx, cy]
    ring
  · simp only [rotK, QK.eval_add, QK.eval_mul, QK.eval_neg, eval_c72K, eval_s72K, ω5, polar, Complex.mul_im, cx, cy]
    ring

lemma Cs_q {j : ℕ} (hj : j < 5) : Cs (6 + 2 * j) = polar ρs ((j + 1) / 5 - αs) := by
  induction j with
  | zero => simp [Cs6_polar]
  | succ j ih =>
    rw [show 6 + 2 * (j + 1) = 8 + 2 * j by ring, Cs_rot (rot_q (by omega)), ih (by omega), ω5, polar_mul,
      mul_one]
    congr 1
    push_cast; ring

end CirclePacking
