import CirclePacking.Surv18Err

/-!
# The optimal configuration of 18 circles

`optimal18`: the 19-circle packing (a centre circle, a ring of six, an outer ring of twelve, container radius
`1 + √2 + √6`) without one circle of its outer ring.  Its points are lattice points of `ℚ(√2, √3)`
(`pointQ`); the kernel checks every distance exactly (`pack18OK`).
-/

open Real

namespace CirclePacking

/-- **The optimal radius for 18 unit circles**: `R₁₈ = 1 + √2 + √6` -/
noncomputable def R18 : ℝ := 1 + √2 + √6

/-- **The optimal configuration of 18 unit circles** (centres; container centred at `0`): the centre `0`; six
centres at distance `2`, at the angles `0, 1/6, …, 5/6` turn; eleven centres at distance `√2 + √6`, at the angles
`1/24, 3/24, …, 21/24` turn.  This is the 19-circle packing without one circle of its outer ring.  (`polar r t` is
the point at distance `r` from `0` and angle `t` turns.) -/
noncomputable def optimal18 (i : Fin 18) : ℂ :=
  if (i : ℕ) = 0 then 0
  else if (i : ℕ) ≤ 6 then polar 2 (((i : ℕ) - 1 : ℕ) / 6)
  else polar (√2 + √6) ((2 * ((i : ℕ) - 7) + 1 : ℕ) / 24)

lemma sqrt6_eq : √6 = √2 * √3 := by
  rw [← Real.sqrt_mul (by norm_num)]; norm_num

lemma R18_eq : R18 = 1 + ρ19 := by
  rw [R18, ρ19, sqrt6_eq]; ring

/-- the exact points of `optimal18`, in `ℚ(√2, √3)` -/
def opt18Q (p : ℕ) : Q23 × Q23 :=
  if p = 0 then (0, 0) else if p ≤ 6 then pointQ ringQ (4 * (p - 1)) else pointQ rho19Q (2 * (p - 7) + 1)

/-- the squared distance of the points `p`, `q` -/
def opt18D2 (p q : ℕ) : Q23 :=
  ((opt18Q p).1 - (opt18Q q).1) * ((opt18Q p).1 - (opt18Q q).1) +
    ((opt18Q p).2 - (opt18Q q).2) * ((opt18Q p).2 - (opt18Q q).2)

/-- every two points are at distance `≥ 2`: the squared distance is exactly `4`, or has a rational lower bound
`≥ 4` -/
def pack18OK : Bool :=
  (List.range 18).all (fun p => (List.range 18).all (fun q =>
    decide (q ≤ p) || decide (opt18D2 p q = 4) || decide (4 ≤ lo23 (opt18D2 p q))))

set_option maxRecDepth 100000 in
theorem pack18OK_true : pack18OK = true := by decide +kernel

lemma optimal18_eq (i : Fin 18) : optimal18 i = ⟨(opt18Q i).1.eval, (opt18Q i).2.eval⟩ := by
  unfold optimal18 opt18Q
  by_cases h0 : (i : ℕ) = 0
  · rw [ite_eq_left h0, ite_eq_left h0]
    apply Complex.ext <;> simp [Q23.eval_zero]
  · by_cases h6 : (i : ℕ) ≤ 6
    · rw [ite_eq_right h0, ite_eq_left h6, ite_eq_right h0, ite_eq_left h6, pointQ_eval]
      have e1 : ringQ.eval = 2 := by simp [ringQ, Q23.eval]
      have e2 : ((4 * ((i : ℕ) - 1) : ℕ) : ℝ) / 24 = (((i : ℕ) - 1 : ℕ) : ℝ) / 6 := by push_cast; ring
      rw [e1, e2]
    · rw [ite_eq_right h0, ite_eq_right h6, ite_eq_right h0, ite_eq_right h6, pointQ_eval, rho19Q_eval, ρ19,
        sqrt6_eq]

lemma two_le_ρ19 : (2 : ℝ) ≤ ρ19 := by
  have h2 : (1 : ℝ) ≤ √2 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have h3 : (1 : ℝ) ≤ √3 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  unfold ρ19
  nlinarith

lemma norm_optimal18 (i : Fin 18) : ‖optimal18 i‖ ≤ ρ19 := by
  have hρ := two_le_ρ19
  unfold optimal18
  split_ifs
  · simp only [norm_zero]; linarith
  · rw [norm_polar (by norm_num)]; exact hρ
  · rw [norm_polar (by positivity), sqrt6_eq]; rfl

lemma dist_optimal18 {i j : Fin 18} (hij : i ≠ j) : 2 ≤ ‖optimal18 i - optimal18 j‖ := by
  -- reduce to `i < j`
  wlog hlt : (i : ℕ) < (j : ℕ) generalizing i j
  · have hne : (i : ℕ) ≠ j := fun h' => hij (Fin.ext h')
    rw [norm_sub_rev]
    exact this hij.symm (by omega)
  have h := pack18OK_true
  unfold pack18OK at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at h
  have hsq : ‖optimal18 i - optimal18 j‖ ^ 2 = (opt18D2 i j).eval := by
    rw [optimal18_eq, optimal18_eq, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, opt18D2, Q23.eval_add, Q23.eval_mul, Q23.eval_sub]
  have h4 : 4 ≤ ‖optimal18 i - optimal18 j‖ ^ 2 := by
    rw [hsq]
    rcases h i i.isLt j j.isLt with (hle | heq) | hlo
    · omega
    · have h4 : (4 : Q23).eval = 4 := by show (Q23.ofQ 4).eval = _; simp
      rw [heq, h4]
    · have := lo23_le (opt18D2 i j)
      have hlo' := (Rat.cast_le (K := ℝ)).mpr hlo
      push_cast at hlo'
      linarith
  nlinarith [norm_nonneg (optimal18 i - optimal18 j)]

/-- **`optimal18` is a packing in the disk of radius `R₁₈`** -/
theorem optimal18_packing :
    (∀ i, ‖optimal18 i‖ + 1 ≤ R18) ∧ ∀ i j, i ≠ j → 2 ≤ ‖optimal18 i - optimal18 j‖ :=
  ⟨fun i => by rw [R18_eq]; linarith [norm_optimal18 i], fun _ _ hij => dist_optimal18 hij⟩

end CirclePacking
