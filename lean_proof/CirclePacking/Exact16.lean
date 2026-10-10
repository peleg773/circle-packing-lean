import CirclePacking.Bridge16

/-!
# The exact 16-circle optimum: explicit radius, explicit configuration

* `H16` (`CirclePacking.Root16`): an integer polynomial of degree 90 (coefficients `H16coeffs`);
  `q16 := sSup {x : ℝ | H16(x) = 0}`, and `q16_isGreatest`: `q16` *is* the largest real root of `H16`.
* `R16 := 1 + √(2 / (1 - q16))`, the optimal container radius.
* `optimal16`: sixteen explicit centres, built from `q16` with arithmetic, `√`, `arccos`, `cos` and `sin`:
  eleven on the circle of radius `ρ = R16 - 1` at the angles `π + mθ` (`m = -5, …, 5`, `θ = arccos q16`), and
  five interior ones `(a, 0)`, `(b, ±c)`, `(d, ±1)` (`CirclePacking.Opt16`).

Main results: `optimal16_eq_C16` (`optimal16` *is* the certified contact solution `c*` of `CirclePacking.CStar16`) and
`R16_eq` (`R16 = 1 + ρ*`).
-/

open Real

namespace CirclePacking

/-- **The optimal radius for 16 unit circles**: `R₁₆ = 1 + √(2 / (1 - q₁₆))`, where `q₁₆` is the largest real root
of the degree-90 integer polynomial `H16`. -/
noncomputable def R16 : ℝ := 1 + √(2 / (1 - q16))

/-! ### The explicit configuration -/

namespace Opt16

/-- radius of the circle through the eleven boundary centres -/
noncomputable def ρ : ℝ := √(2 / (1 - q16))

/-- angle between consecutive boundary centres, seen from the centre of the container -/
noncomputable def θ : ℝ := arccos q16

/-- the boundary centre at angle `π + mθ`: `-ρ e^{imθ}` -/
noncomputable def B (m : ℤ) : ℂ := ⟨-ρ * cos (m * θ), -ρ * sin (m * θ)⟩

/-- the interior centre `(a, 0)` touches the boundary centre `B (-5)` -/
noncomputable def a : ℝ := -ρ * cos (5 * θ) - √(4 - (ρ * sin (5 * θ)) ^ 2)

/-- the interior centre `(d, 1)` touches the boundary centre `B (-1)` -/
noncomputable def d : ℝ := -ρ * cos θ + √(4 - (1 - ρ * sin θ) ^ 2)

/-- denominator of `b` -/
noncomputable def D : ℝ := a + ρ * cos (3 * θ) - (a - d) * (ρ * sin (3 * θ))

/-- the interior centre `(b, c)` touches `(a, 0)`, `(d, 1)` and `B (-3)` -/
noncomputable def b : ℝ := (a ^ 2 - ρ ^ 2 + ρ * sin (3 * θ) * (d ^ 2 + 1 - a ^ 2)) / (2 * D)

/-- see `b` -/
noncomputable def c : ℝ := (a - d) * b + (d ^ 2 + 1 - a ^ 2) / 2

end Opt16

open Opt16 in
/-- **The optimal configuration of 16 unit circles** (centres; container centred at `0`): five interior centres
`(a, 0)`, `(b, ±c)`, `(d, ±1)`, and eleven centres `B m = ρ (cos (π + mθ), sin (π + mθ))`, `m = -5, …, 5`, on the
circle of radius `ρ = R16 - 1`.  All parameters are explicit functions of `q16` (`CirclePacking.Opt16`). -/
noncomputable def optimal16 : Fin 16 → ℂ :=
  ![⟨a, 0⟩, ⟨b, c⟩, ⟨d, 1⟩, ⟨d, -1⟩, ⟨b, -c⟩,
    B (-5), B (-4), B (-3), B (-2), B (-1), B 0, B 1, B 2, B 3, B 4, B 5]

/-! ### `H16` and `q16`; `R16 = 1 + ρ*` -/

/-- **`q16` is the largest real root of `H16`.** -/
theorem q16_isGreatest : IsGreatest {x : ℝ | Polynomial.aeval x H16 = 0} q16 := by
  rw [q16_eq_qg]; exact isGreatest_of_root qg_bounds H16_qg

lemma ZPoly.coeff_toPoly (p : ZPoly) (i : ℕ) : (ZPoly.toPoly p).coeff i = p.getD i 0 := by
  induction p generalizing i with
  | nil => simp [ZPoly.toPoly]
  | cons a p ih =>
    cases i with
    | zero =>
      simp only [ZPoly.toPoly, Polynomial.coeff_add, Polynomial.coeff_C_zero, Polynomial.mul_coeff_zero,
        Polynomial.coeff_X_zero, zero_mul, add_zero, List.getD_cons_zero]
    | succ i =>
      simp only [ZPoly.toPoly, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_X_mul, ih,
        List.getD_cons_succ, Nat.succ_ne_zero, ite_false, zero_add]

/-- `H16 = ∑ᵢ H16coeffs[i] Xⁱ` -/
lemma H16_coeff (i : ℕ) : H16.coeff i = H16coeffs.getD i 0 := by
  rw [H16]; exact ZPoly.coeff_toPoly _ _

/-- **`H16` has degree 90.** -/
theorem H16_natDegree : H16.natDegree = 90 := by
  have hlen : H16coeffs.length = 91 := by decide +kernel
  apply le_antisymm
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [H16_coeff, List.getD_eq_default _ _ (by rw [hlen]; exact_mod_cast hN)]
  · apply Polynomial.le_natDegree_of_ne_zero
    rw [H16_coeff]
    decide +kernel

lemma ρ_eq : Opt16.ρ = ρ16 := ρ16_eq.symm

lemma R16_eq : R16 = 1 + ρ16 := by rw [R16, ← ρ16_eq]

lemma cos_θ : cos Opt16.θ = qg := by
  rw [Opt16.θ, q16_eq_qg]; exact cos_arccos (by linarith [qg_pos]) qg_lt_one.le

lemma sin_θ : sin Opt16.θ = sg := by
  rw [Opt16.θ, q16_eq_qg, sin_arccos]; rfl

/-- de Moivre: `v^m = e^{imθ}` -/
lemma v16_pow_eq (m : ℕ) : v16 ^ m = ⟨cos (m * Opt16.θ), sin (m * Opt16.θ)⟩ := by
  have hv : v16 = Complex.exp (Opt16.θ * Complex.I) := by
    apply Complex.ext
    · rw [Complex.exp_ofReal_mul_I_re, cos_θ]; rfl
    · rw [Complex.exp_ofReal_mul_I_im, sin_θ]; rfl
  rw [hv, ← Complex.exp_nat_mul, ← mul_assoc,
    show (m : ℂ) * (Opt16.θ : ℂ) = ((m * Opt16.θ : ℝ) : ℂ) by push_cast; ring]
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re]
  · rw [Complex.exp_ofReal_mul_I_im]

/-- the boundary centres of `c*` are the `B m` -/
lemma C16_eq_B {k : ℕ} (h5 : 5 ≤ k) (h15 : k ≤ 15) : C16 k = Opt16.B ((k : ℤ) - 10) := by
  rcases le_or_gt 10 k with h | h
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [C16_ten_add (by omega), v16_pow_eq, Opt16.B, ρ_eq]
    have : (((10 + m : ℕ) : ℤ) - 10 : ℤ) = (m : ℤ) := by push_cast; ring
    rw [this]
    apply Complex.ext <;> simp
  · obtain ⟨m, hm, rfl⟩ : ∃ m, m ≤ 5 ∧ k = 10 - m := ⟨10 - k, by omega, by omega⟩
    rw [C16_ten_sub hm, ← map_pow, v16_pow_eq, Opt16.B, ρ_eq]
    have : (((10 - m : ℕ) : ℤ) - 10 : ℤ) = -(m : ℤ) := by omega
    rw [this]
    apply Complex.ext <;> simp [neg_mul, cos_neg, sin_neg]

lemma u16_bnd_re {k : ℕ} (h5 : 5 ≤ k) (h15 : k ≤ 15) :
    u16 (2 * k) = -ρ16 * cos (((k : ℤ) - 10 : ℤ) * Opt16.θ) := by
  have h := congrArg Complex.re (C16_eq_B h5 h15)
  simp only [C16, Opt16.B, ρ_eq] at h
  exact h

lemma u16_bnd_im {k : ℕ} (h5 : 5 ≤ k) (h15 : k ≤ 15) :
    u16 (2 * k + 1) = -ρ16 * sin (((k : ℤ) - 10 : ℤ) * Opt16.θ) := by
  have h := congrArg Complex.im (C16_eq_B h5 h15)
  simp only [C16, Opt16.B, ρ_eq] at h
  exact h

/-! ### The interior centres -/

lemma near_lt {i j : ℕ} (hi : i < 33) (hj : j < 33)
    (h : n16K.utq i + 1 / 2 ^ 80 < n16K.utq j - 1 / 2 ^ 80) : u16 i < u16 j := by
  have h1 := (u16_near' hi).2
  have h2 := (u16_near' hj).1
  have h' := (Rat.cast_lt (K := ℝ)).mpr h
  push_cast at h'
  linarith

lemma u16_0_lt : u16 0 < u16 10 := near_lt (by norm_num) (by norm_num) (by decide +kernel)
lemma u16_18_lt : u16 18 < u16 4 := near_lt (by norm_num) (by norm_num) (by decide +kernel)

/-- the denominator `D` is negative at `c*` -/
lemma D16_neg : u16 0 - u16 14 - (u16 0 - u16 4) * u16 15 < 0 := by
  have e0 := u16_near' (k := 0) (by norm_num)
  have e4 := u16_near' (k := 4) (by norm_num)
  have e14 := u16_near' (k := 14) (by norm_num)
  have e15 := u16_near' (k := 15) (by norm_num)
  have c1 : (0 : ℚ) < n16K.utq 0 - n16K.utq 4 - 2 / 2 ^ 80 := by decide +kernel
  have c2 : (0 : ℚ) < n16K.utq 15 - 1 / 2 ^ 80 := by decide +kernel
  have c3 : n16K.utq 0 + 1 / 2 ^ 80 - (n16K.utq 14 - 1 / 2 ^ 80) -
      (n16K.utq 0 - n16K.utq 4 - 2 / 2 ^ 80) * (n16K.utq 15 - 1 / 2 ^ 80) < 0 := by decide +kernel
  have c1' := (Rat.cast_lt (K := ℝ)).mpr c1
  have c2' := (Rat.cast_lt (K := ℝ)).mpr c2
  have c3' := (Rat.cast_lt (K := ℝ)).mpr c3
  push_cast at c1' c2' c3'
  have hm : ((n16K.utq 0 : ℝ) - n16K.utq 4 - 2 / 2 ^ 80) * (n16K.utq 15 - 1 / 2 ^ 80) ≤
      (u16 0 - u16 4) * u16 15 :=
    mul_le_mul (by linarith) (by linarith) c2'.le (by linarith)
  linarith

lemma u16_10 : u16 10 = -ρ16 * cos (5 * Opt16.θ) := by
  have h := u16_bnd_re (k := 5) (by norm_num) (by norm_num)
  norm_num at h; linear_combination h
lemma u16_11 : u16 11 = ρ16 * sin (5 * Opt16.θ) := by
  have h := u16_bnd_im (k := 5) (by norm_num) (by norm_num)
  norm_num at h; linear_combination h
lemma u16_14 : u16 14 = -ρ16 * cos (3 * Opt16.θ) := by
  have h := u16_bnd_re (k := 7) (by norm_num) (by norm_num)
  norm_num at h; linear_combination h
lemma u16_15 : u16 15 = ρ16 * sin (3 * Opt16.θ) := by
  have h := u16_bnd_im (k := 7) (by norm_num) (by norm_num)
  norm_num at h; linear_combination h
lemma u16_18 : u16 18 = -ρ16 * cos Opt16.θ := by
  have h := u16_bnd_re (k := 9) (by norm_num) (by norm_num)
  norm_num at h; linear_combination h
lemma u16_19 : u16 19 = ρ16 * sin Opt16.θ := by
  have h := u16_bnd_im (k := 9) (by norm_num) (by norm_num)
  norm_num at h; linear_combination h

lemma a_eq : Opt16.a = u16 0 := by
  have c05 := contact16 (r := 2) (i := 0) (j := 5) (by norm_num) rfl rfl
  norm_num at c05
  rw [C16_gauge] at c05
  have hsq : 4 - (ρ16 * sin (5 * Opt16.θ)) ^ 2 = (u16 0 - u16 10) ^ 2 := by
    rw [← u16_11]; linear_combination -c05
  rw [Opt16.a, ρ_eq, hsq, Real.sqrt_sq_eq_abs, abs_of_neg (sub_neg.mpr u16_0_lt), u16_10]
  ring

lemma d_eq : Opt16.d = u16 4 := by
  have c29 := contact16 (r := 7) (i := 2) (j := 9) (by norm_num) rfl rfl
  norm_num at c29
  rw [u16_5] at c29
  have hsq : 4 - (1 - ρ16 * sin Opt16.θ) ^ 2 = (u16 4 - u16 18) ^ 2 := by
    rw [← u16_19]; linear_combination -c29
  rw [Opt16.d, ρ_eq, hsq, Real.sqrt_sq_eq_abs, abs_of_pos (sub_pos.mpr u16_18_lt), u16_18]
  ring

lemma D_eq : Opt16.D = u16 0 - u16 14 - (u16 0 - u16 4) * u16 15 := by
  rw [Opt16.D, a_eq, d_eq, ρ_eq, u16_14, u16_15]; ring

/-- the two linear relations behind `b` and `c` -/
lemma bc_rel : 2 * u16 3 = 2 * (u16 0 - u16 4) * u16 2 + u16 4 ^ 2 + 1 - u16 0 ^ 2 ∧
    2 * u16 2 * (u16 0 - u16 14 - (u16 0 - u16 4) * u16 15) =
      u16 0 ^ 2 - ρ16 ^ 2 + u16 15 * (u16 4 ^ 2 + 1 - u16 0 ^ 2) := by
  have c01 := contact16 (r := 0) (i := 0) (j := 1) (by norm_num) rfl rfl
  have c12 := contact16 (r := 4) (i := 1) (j := 2) (by norm_num) rfl rfl
  have c17 := contact16 (r := 5) (i := 1) (j := 7) (by norm_num) rfl rfl
  norm_num at c01 c12 c17
  rw [C16_gauge] at c01
  rw [u16_5] at c12
  have hb : u16 14 ^ 2 + u16 15 ^ 2 = ρ16 ^ 2 := by
    rw [u16_14, u16_15]; linear_combination ρ16 ^ 2 * sin_sq_add_cos_sq (3 * Opt16.θ)
  have hi : 2 * u16 3 = 2 * (u16 0 - u16 4) * u16 2 + u16 4 ^ 2 + 1 - u16 0 ^ 2 := by
    linear_combination c01 - c12
  exact ⟨hi, by linear_combination c17 - c01 - hb + u16 15 * hi⟩

lemma b_eq : Opt16.b = u16 2 := by
  have hD := D16_neg
  rw [Opt16.b, D_eq, a_eq, d_eq, ρ_eq, ← u16_15, div_eq_iff (mul_ne_zero two_ne_zero hD.ne)]
  linear_combination -bc_rel.2

lemma c_eq : Opt16.c = u16 3 := by
  rw [Opt16.c, a_eq, d_eq, b_eq]; linear_combination -bc_rel.1 / 2

/-- **`optimal16` is the certified optimum `c*`.** -/
theorem optimal16_eq_C16 (i : Fin 16) : optimal16 i = C16 i := by
  have m1 := C16_mirror (p := 1) (by norm_num)
  have m2 := C16_mirror (p := 2) (by norm_num)
  simp only [show sig16 1 = 4 from rfl, show sig16 2 = 3 from rfl] at m1 m2
  fin_cases i
  · apply Complex.ext
    · simp [optimal16, C16, a_eq]
    · simp [optimal16, C16, C16_gauge]
  · apply Complex.ext
    · simp [optimal16, C16, b_eq]
    · simp [optimal16, C16, c_eq]
  · apply Complex.ext
    · simp [optimal16, C16, d_eq]
    · simp [optimal16, C16, u16_5]
  · rw [show ((⟨3, by norm_num⟩ : Fin 16) : ℕ) = 3 from rfl, m2]
    apply Complex.ext
    · simp [optimal16, C16, d_eq]
    · simp [optimal16, C16, u16_5]
  · rw [show ((⟨4, by norm_num⟩ : Fin 16) : ℕ) = 4 from rfl, m1]
    apply Complex.ext
    · simp [optimal16, C16, b_eq]
    · simp [optimal16, C16, c_eq]
  all_goals
    rw [C16_eq_B (by simp) (by simp)]
    simp [optimal16]

end CirclePacking
