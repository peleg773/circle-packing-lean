import CirclePacking.Surv18Hex
import CirclePacking.Lattice18
import CirclePacking.Q23Bounds

/-!
# Survivors of 18 circles: closeness bounds

* `interiorErrG_sound`, `boundaryErrG_sound`: the bounds of `C18Surv.lean`, for a point given by polar
  brackets (as `interiorErr17_sound`, `boundaryErr17_sound` in `Surv17.lean`).
* `radLo_le`, `le_radHi`, `angLo_le`, `le_angHi`: the brackets contain the radius of each code (`0`, `2`, `2√2`)
  and the angle `a/24` turn.
* `ρ₁₉ = √2 + √2 √3` (`= √6 + √2`): `rho19Q.eval = ρ19`, `ρ19² = 8 + 4√3 ≤ rho2Hi19 / S²`.
-/

open Real

namespace CirclePacking

lemma interiorErrG_sound {I : IBox} {rl rh al ah : ℤ} {e : ℚ} (h : interiorErrG I rl rh al ah = some e)
    {s ψ r φ : ℝ} (hI : InI I s ψ) (hr1 : sc rl ≤ r) (hr2 : r ≤ sc rh) (hφ1 : sc al ≤ φ) (hφ2 : φ ≤ sc ah) :
    ‖polar s ψ - polar r φ‖ ^ 2 ≤ e := by
  unfold interiorErrG at h
  by_cases h00 : rl = 0 ∧ rh = 0
  · -- the centre
    rw [if_pos h00] at h
    split_ifs at h with hslo
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨hrl, hrh⟩ := h00
    subst hrl; subst hrh
    have hr : r = 0 := le_antisymm (by simpa [sc] using hr2) (by simpa [sc] using hr1)
    subst hr
    obtain ⟨hI1, hI2, -, -⟩ := hI
    have hs0 : 0 ≤ s := le_trans (sc_nonneg hslo) hI1
    have e0 : polar 0 φ = 0 := by simp [polar]; rfl
    rw [e0, sub_zero, norm_polar hs0]
    have hS := S_pos
    have : s ≤ sc I.shi := hI2
    have hsq : s ^ 2 ≤ sc I.shi ^ 2 := pow_le_pow_left₀ hs0 this 2
    unfold sc at hsq
    push_cast
    rw [div_pow] at hsq
    calc s ^ 2 ≤ (I.shi : ℝ) ^ 2 / (S : ℝ) ^ 2 := hsq
      _ = (I.shi : ℝ) * I.shi / ((S : ℝ) * S) := by ring
  rw [if_neg h00] at h
  simp only at h
  split_ifs at h with hc
  obtain ⟨hD0, hD1, hslo, hrl⟩ := hc
  simp only [Option.some.injEq] at h
  subst h
  set D := max (I.phi - al) (ah - I.plo) with hD
  obtain ⟨hI1, hI2, hI3, hI4⟩ := hI
  have hs0 : 0 ≤ s := le_trans (sc_nonneg hslo) hI1
  have hr0 : 0 ≤ r := le_trans (sc_nonneg hrl) hr1
  have hdist : |ψ - φ - ((0 : ℤ) : ℝ)| ≤ sc D := by
    rw [Int.cast_zero, sub_zero, abs_le]
    have h1 : sc (I.phi - al) ≤ sc D := sc_le_iff.mpr (le_max_left _ _)
    have h2 : sc (ah - I.plo) ≤ sc D := sc_le_iff.mpr (le_max_right _ _)
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

lemma boundaryErrG_sound {W : ℤ × ℤ} {al ah : ℤ} {e : ℚ} (h : boundaryErrG W al ah = some e)
    {ρs ρ y θ : ℝ} (hρs : 0 < ρs) (hrho : ρs ^ 2 ≤ (rho2Hi19 : ℝ) / ((S : ℝ) * S))
    (hρ1 : ρs - epsR ≤ ρ) (hρ2 : ρ ≤ ρs) (hρ0 : 0 ≤ ρ) (hy1 : sc W.1 ≤ y) (hy2 : y ≤ sc W.2)
    (hθ1 : sc al ≤ θ) (hθ2 : θ ≤ sc ah) :
    ‖polar ρ y - polar ρs θ‖ ^ 2 ≤ e := by
  unfold boundaryErrG at h
  simp only at h
  split_ifs at h with hc
  obtain ⟨hD0, hD1⟩ := hc
  simp only [Option.some.injEq] at h
  subst h
  set D := max (W.2 - al) (ah - W.1) with hD
  rw [normSq_polar_sub]
  have hdist : |y - θ - ((0 : ℤ) : ℝ)| ≤ sc D := by
    rw [Int.cast_zero, sub_zero, abs_le]
    have h1 : sc (W.2 - al) ≤ sc D := sc_le_iff.mpr (le_max_left _ _)
    have h2 : sc (ah - W.1) ≤ sc D := sc_le_iff.mpr (le_max_right _ _)
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
  have h3 : 2 * ρs ^ 2 * (1 - sc (cosZ D)) ≤
      2 * ((rho2Hi19 : ℝ) / ((S : ℝ) * S)) * (1 - sc (cosZ D)) := by
    have : 0 ≤ 1 - sc (cosZ D) := by linarith
    nlinarith
  have e2 : 2 * ((rho2Hi19 : ℝ) / ((S : ℝ) * S)) * (1 - sc (cosZ D)) =
      ((2 * rho2Hi19 * (S - cosZ D) : ℤ) : ℝ) / ((S : ℝ) * S * S) := by
    unfold sc; push_cast; field_simp
  push_cast
  rw [e2] at h3
  push_cast at h3
  have : ((epsR : ℚ) : ℝ) * ((epsR : ℚ) : ℝ) = ((epsR : ℚ) : ℝ) ^ 2 := by ring
  linarith

/-! ### Brackets -/

/-- the radius of a code -/
noncomputable def radOf (c : ℕ) : ℝ := if c = 0 then 0 else if c = 1 then 2 else 2 * √2

theorem s2_bracket : (3109888511975 : ℚ) ^ 2 ≤ 8 * (S : ℚ) ^ 2 ∧ 8 * (S : ℚ) ^ 2 ≤ (3109888511976 : ℚ) ^ 2 := by
  decide +kernel

lemma radLo_le (c : ℕ) : sc (radLo c) ≤ radOf c := by
  unfold radLo radOf
  split_ifs with h0 h1
  · simp [sc]
  · simp [sc, S_eq]; norm_num
  · -- `⌊2√2 S⌋ / S ≤ 2√2`
    have hb := s2_bracket.1
    have hS := S_pos
    have hb' : ((3109888511975 : ℚ) : ℝ) ^ 2 ≤ 8 * ((S : ℚ) : ℝ) ^ 2 := by exact_mod_cast hb
    push_cast at hb'
    have h8 : (8 : ℝ) = (2 * √2) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]; norm_num
    rw [h8, ← mul_pow] at hb'
    have hpos : 0 ≤ 2 * √2 * (S : ℝ) := by positivity
    have := (sq_le_sq₀ (by norm_num) hpos).mp hb'
    unfold sc; rw [div_le_iff₀ hS]; push_cast; linarith

lemma le_radHi (c : ℕ) : radOf c ≤ sc (radHi c) := by
  unfold radHi radOf
  split_ifs with h0 h1
  · simp [sc]
  · simp [sc, S_eq]; norm_num
  · have hb := s2_bracket.2
    have hS := S_pos
    have hb' : 8 * ((S : ℚ) : ℝ) ^ 2 ≤ ((3109888511976 : ℚ) : ℝ) ^ 2 := by exact_mod_cast hb
    push_cast at hb'
    have h8 : (8 : ℝ) = (2 * √2) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]; norm_num
    rw [h8, ← mul_pow] at hb'
    have := (sq_le_sq₀ (by positivity) (by norm_num)).mp hb'
    unfold sc; rw [le_div_iff₀ hS]; push_cast; linarith

lemma angLo_le (a : ℕ) : sc (angLo a) ≤ (a : ℝ) / 24 := by
  unfold angLo sc
  have hS := S_pos
  rw [div_le_div_iff₀ hS (by norm_num)]
  have h : ((a : ℤ) * S / 24 : ℤ) * 24 ≤ (a : ℤ) * S := Int.ediv_mul_le _ (by norm_num)
  have h' : (((a : ℤ) * S / 24 : ℤ) : ℝ) * 24 ≤ ((a : ℤ) * S : ℤ) := by exact_mod_cast h
  push_cast at h' ⊢
  linarith

lemma le_angHi (a : ℕ) : (a : ℝ) / 24 ≤ sc (angHi a) := by
  unfold angHi sc
  have hS := S_pos
  rw [div_le_div_iff₀ (by norm_num) hS]
  have h : (a : ℤ) * S < ((a : ℤ) * S + 23) / 24 * 24 + 1 := by omega
  have h2 : (a : ℤ) * S ≤ ((a : ℤ) * S + 23) / 24 * 24 := by omega
  have h' : (((a : ℤ) * S : ℤ) : ℝ) ≤ (((a : ℤ) * S + 23) / 24 * 24 : ℤ) := by exact_mod_cast h2
  push_cast at h' ⊢
  linarith

/-! ### `ρ₁₉` -/

/-- **`ρ₁₉ = √6 + √2`** (written `√2 + √2 √3`) -/
noncomputable def ρ19 : ℝ := √2 + √2 * √3

lemma rho19Q_eval : rho19Q.eval = ρ19 := by simp [rho19Q, Q23.eval, ρ19]

lemma ρ19_sq : ρ19 ^ 2 = 8 + 4 * √3 := by
  have h2 := Q23.sq2
  have h3 := Q23.sq3
  unfold ρ19
  nlinarith

lemma ρ19_pos : 0 < ρ19 := by unfold ρ19; positivity

theorem rho2Hi19_ok : (8 : ℚ) * (S : ℚ) ^ 2 + 4 * rh3' * (S : ℚ) ^ 2 ≤ (rho2Hi19 : ℚ) := by decide +kernel

lemma ρ19_sq_le : ρ19 ^ 2 ≤ (rho2Hi19 : ℝ) / ((S : ℝ) * S) := by
  rw [ρ19_sq, le_div_iff₀ (by have := S_pos; positivity)]
  have h := rho2Hi19_ok
  have h' : ((8 * (S : ℚ) ^ 2 + 4 * rh3' * (S : ℚ) ^ 2 : ℚ) : ℝ) ≤ ((rho2Hi19 : ℚ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  have h3 := sqrt3_bounds.2
  have hS := S_pos
  nlinarith

end CirclePacking
