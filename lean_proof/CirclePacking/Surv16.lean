import CirclePacking.Surv
import C16Compute

/-!
# Survivors of the record case of 16 circles: windows and closeness

The analogue of `Surv.lean` for `n = 16`: the eleven boundary points of a configuration in a box passing
`survOK16` lie one per window, and each point is close to the corresponding point of `c*` (given by
certified polar brackets).
-/

open Real Finset

namespace CirclePacking

lemma sc_wStart16_eleven : sc (wStart16 11) = sc (win16 0).1 + 1 := by
  simp [wStart16, sc_add, sc_S]

lemma wStart16_lt {w : ℕ} (hw : w < 11) : wStart16 w = (win16 w).1 := by
  simp [wStart16, show w ≠ 11 by omega]

/-- **Assignment of the eleven boundary points to the windows.** -/
theorem surv_assign16 {δ : ℤ} {jf : ℕ} {arcs : List (ℤ × ℤ)} (hδ : 0 < δ)
    (hbad : ∀ w < 11, ((liftArcs arcs).any (fun q => decide (q.1 < (badI16 w).1 ∧ (badI16 w).2 < q.2)) ||
      decide (greedyFromInterval arcs δ (badI16 w).1 (badI16 w).2 jf 10 < 11)) = true)
    (hwid : ∀ w < 11, (win16 w).2 - (win16 w).1 < δ)
    (a : Fin 11 → ℝ)
    (hsep : ∀ b b', b ≠ b' → ∀ m : ℤ, sc δ ≤ |a b - a b' - m|)
    (hall : ∀ b, ∀ p ∈ arcs, Avoids (a b) p) :
    ∃ σ : Fin 11 → Fin 11, Function.Injective σ ∧ ∀ w : Fin 11, ∃ m : ℤ,
      sc (win16 w).1 ≤ a (σ w) + m ∧ a (σ w) + m ≤ sc (win16 w).2 := by
  have hin : ∀ b : Fin 11, ∃ w : Fin 11, ∃ m : ℤ,
      sc (win16 w).1 ≤ a b + m ∧ a b + m ≤ sc (win16 w).2 := by
    intro b
    set L := sc (win16 0).1
    set m : ℤ := ⌈L - a b⌉
    have hm1 : L ≤ a b + m := by have := Int.le_ceil (L - a b); linarith
    have hm2 : a b + m ≤ L + 1 := by have := Int.ceil_lt_add_one (L - a b); linarith
    have h0 : sc (wStart16 0) ≤ a b + m := by rw [wStart16_lt (by norm_num)]; exact hm1
    have h11 : a b + m ≤ sc (wStart16 (10 + 1)) := by rw [sc_wStart16_eleven]; exact hm2
    obtain ⟨w, hw, hw1, hw2⟩ := exists_window (fun w => sc (wStart16 w)) 10 h0 h11
    rw [wStart16_lt (by omega)] at hw1
    by_cases hx : a b + m ≤ sc (win16 w).2
    · exact ⟨⟨w, by omega⟩, m, hw1, hx⟩
    · exfalso
      have hx' : sc (badI16 w).1 ≤ a b + m := by simp only [badI16]; linarith
      have hx'' : a b + m ≤ sc (badI16 w).2 := by simp only [badI16]; exact hw2
      have hb := hbad w (by omega)
      simp only [Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq] at hb
      rcases hb with ⟨q, hq, hq1, hq2⟩ | hg
      · have hav : ∀ p ∈ arcs, Avoids (a b + m) p := fun p hp => (hall b p hp).shift m
        exact avoids_lift hav q hq ⟨lt_of_lt_of_le (sc_lt_iff.mpr hq1) hx',
          lt_of_le_of_lt hx'' (sc_lt_iff.mpr hq2)⟩
      · have := card_le_greedyFromInterval arcs δ (badI16 w).1 (badI16 w).2 hδ jf 10
          (by norm_num) a hsep hall b m hx' hx''
        omega
  choose wf mf hwf using hin
  have hinj : Function.Injective wf := by
    intro b b' heq
    by_contra hne
    have h1 := hwf b
    have h2 := hwf b'
    rw [heq] at h1
    have hw := hwid (wf b') (wf b').isLt
    have hwR : sc (win16 (wf b')).2 - sc (win16 (wf b')).1 < sc δ := by
      rw [← sc_sub]; exact sc_lt_iff.mpr hw
    have hs := hsep b b' hne (mf b' - mf b)
    push_cast at hs
    have : |a b - a b' - (mf b' - mf b)| < sc δ := by
      rw [abs_lt]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    linarith
  have hbij : Function.Bijective wf := Finite.injective_iff_bijective.mp hinj
  set e := Equiv.ofBijective wf hbij
  refine ⟨e.symm, e.symm.injective, ?_⟩
  intro w
  have h := hwf (e.symm w)
  have he : wf (e.symm w) = w := e.apply_symm_apply w
  rw [he] at h
  exact ⟨_, h⟩

/-! ### Closeness of a single point -/

lemma interiorErr16_sound {I : IBox} {p : ℕ} {e : ℚ} (h : interiorErr16 I p = some e) {s ψ r φ : ℝ}
    (hI : InI I s ψ) (hr1 : sc (r16Lo.getD p 0) ≤ r) (hr2 : r ≤ sc (r16Hi.getD p 0))
    (hφ1 : sc (a16Lo.getD p 0) ≤ φ) (hφ2 : φ ≤ sc (a16Hi.getD p 0)) :
    ‖polar s ψ - polar r φ‖ ^ 2 ≤ e := by
  unfold interiorErr16 at h
  simp only at h
  split_ifs at h with hc
  obtain ⟨hD0, hD1, hslo, hrl⟩ := hc
  simp only [Option.some.injEq] at h
  subst h
  set D := max (I.phi - a16Lo.getD p 0) (a16Hi.getD p 0 - I.plo) with hD
  obtain ⟨hI1, hI2, hI3, hI4⟩ := hI
  have hs0 : 0 ≤ s := le_trans (sc_nonneg hslo) hI1
  have hr0 : 0 ≤ r := le_trans (sc_nonneg hrl) hr1
  have hdist : |ψ - φ - ((0 : ℤ) : ℝ)| ≤ sc D := by
    rw [Int.cast_zero, sub_zero, abs_le]
    have h1 : sc (I.phi - a16Lo.getD p 0) ≤ sc D := sc_le_iff.mpr (le_max_left _ _)
    have h2 : sc (a16Hi.getD p 0 - I.plo) ≤ sc D := sc_le_iff.mpr (le_max_right _ _)
    rw [sc_sub] at h1 h2
    constructor <;> linarith
  have hcos1 := cos_turn_le (half_of_two_le hD1) hdist
  have hcos2 := cosZ_sc hD0 hD1
  rw [normSq_polar_sub]
  have hprod : 0 ≤ s * r := mul_nonneg hs0 hr0
  have step : s ^ 2 + r ^ 2 - 2 * s * r * Real.cos (2 * π * (ψ - φ)) ≤
      s ^ 2 + r ^ 2 - 2 * sc (cosZ D) * s * r := by
    nlinarith [mul_le_mul_of_nonneg_left (le_trans hcos2 hcos1) hprod]
  refine le_trans step ?_
  simp only [Rat.cast_div, Rat.cast_intCast, Rat.cast_mul, Int.cast_mul]
  apply Q_le_corners hI1 hI2 hr1 hr2 <;> apply corner_le
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  · exact le_trans (le_max_left _ _) (le_max_right _ _)
  · exact le_trans (le_max_right _ _) (le_max_right _ _)

lemma boundaryErr16_sound {W : ℤ × ℤ} {w : ℕ} {e : ℚ} (h : boundaryErr16 W w = some e)
    {ρs ρ y θ : ℝ} (hρs : 0 < ρs) (hrho : ρs ^ 2 ≤ (rho2Hi16 : ℝ) / ((S : ℝ) * S))
    (hρ1 : ρs - epsR ≤ ρ) (hρ2 : ρ ≤ ρs) (hρ0 : 0 ≤ ρ) (hy1 : sc W.1 ≤ y) (hy2 : y ≤ sc W.2)
    (hθ1 : sc (a16Lo.getD (5 + w) 0) ≤ θ) (hθ2 : θ ≤ sc (a16Hi.getD (5 + w) 0)) :
    ‖polar ρ y - polar ρs θ‖ ^ 2 ≤ e := by
  unfold boundaryErr16 at h
  simp only at h
  split_ifs at h with hc
  obtain ⟨hD0, hD1⟩ := hc
  simp only [Option.some.injEq] at h
  subst h
  set D := max (W.2 - a16Lo.getD (5 + w) 0) (a16Hi.getD (5 + w) 0 - W.1) with hD
  rw [normSq_polar_sub]
  have hdist : |y - θ - ((0 : ℤ) : ℝ)| ≤ sc D := by
    rw [Int.cast_zero, sub_zero, abs_le]
    have h1 : sc (W.2 - a16Lo.getD (5 + w) 0) ≤ sc D := sc_le_iff.mpr (le_max_left _ _)
    have h2 : sc (a16Hi.getD (5 + w) 0 - W.1) ≤ sc D := sc_le_iff.mpr (le_max_right _ _)
    rw [sc_sub] at h1 h2
    constructor <;> linarith
  have hcos1 := cos_turn_le (half_of_two_le hD1) hdist
  have hcos2 := cosZ_sc hD0 hD1
  set C := Real.cos (2 * π * (y - θ))
  have hC1 : C ≤ 1 := Real.cos_le_one _
  have hcC : sc (cosZ D) ≤ C := le_trans hcos2 hcos1
  have hS := S_pos
  have heps : ((epsR : ℚ) : ℝ) = 1 / 1000000 := by unfold epsR; push_cast; ring
  have e1 : ρ ^ 2 + ρs ^ 2 - 2 * ρ * ρs * C = (ρs - ρ) ^ 2 + 2 * (ρ * ρs) * (1 - C) := by ring
  rw [e1]
  have h1 : (ρs - ρ) ^ 2 ≤ ((epsR : ℚ) : ℝ) ^ 2 := by
    rw [heps]; have : ρs - ρ ≤ 1 / 1000000 := by rw [heps] at hρ1; linarith
    nlinarith
  have h2 : 2 * (ρ * ρs) * (1 - C) ≤ 2 * ρs ^ 2 * (1 - sc (cosZ D)) := by
    have : ρ * ρs ≤ ρs ^ 2 := by nlinarith
    have : 0 ≤ ρ * ρs := by positivity
    nlinarith
  have h3 : 2 * ρs ^ 2 * (1 - sc (cosZ D)) ≤ 2 * ((rho2Hi16 : ℝ) / ((S : ℝ) * S)) * (1 - sc (cosZ D)) := by
    have : 0 ≤ 1 - sc (cosZ D) := by linarith
    nlinarith
  have e2 : 2 * ((rho2Hi16 : ℝ) / ((S : ℝ) * S)) * (1 - sc (cosZ D)) =
      ((2 * rho2Hi16 * (S - cosZ D) : ℤ) : ℝ) / ((S : ℝ) * S * S) := by
    unfold sc; push_cast; field_simp
  push_cast
  rw [e2] at h3
  push_cast at h3
  have : ((epsR : ℚ) : ℝ) * ((epsR : ℚ) : ℝ) = ((epsR : ℚ) : ℝ) ^ 2 := by ring
  linarith

end CirclePacking
