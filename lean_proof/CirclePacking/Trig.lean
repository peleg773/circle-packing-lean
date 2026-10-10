import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Certified bounds for cos and sin from alternating partial sums
-/

open Real Finset

namespace CirclePacking

/-- The `i`-th term of the cosine series (without sign). -/
noncomputable def cosTerm (y : ℝ) (i : ℕ) : ℝ := y ^ (2 * i) / ((2 * i).factorial : ℝ)

/-- The `i`-th term of the sine series (without sign). -/
noncomputable def sinTerm (y : ℝ) (i : ℕ) : ℝ := y ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ)

lemma cosTerm_antitone {y : ℝ} (hy : y ^ 2 ≤ 2) : Antitone (cosTerm y) := by
  refine antitone_nat_of_succ_le (fun i => ?_)
  unfold cosTerm
  have h1 : (2 * (i + 1)) = (2 * i + 1) + 1 := by ring
  rw [h1, Nat.factorial_succ, Nat.factorial_succ]
  have hf : (0 : ℝ) < ((2 * i).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hp : (0 : ℝ) ≤ y ^ (2 * i) := by rw [pow_mul]; positivity
  have hf2 : (0 : ℝ) < (((2 * i + 1 + 1) * ((2 * i + 1) * (2 * i).factorial) : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (Nat.factorial_pos _))
  rw [div_le_div_iff₀ hf2 hf]
  push_cast
  have : y ^ (2 * i + 1 + 1) = y ^ (2 * i) * y ^ 2 := by ring
  rw [this]
  have hi : (2 : ℝ) ≤ ((2 * i + 1 + 1 : ℕ) : ℝ) * ((2 * i + 1 : ℕ) : ℝ) := by
    push_cast; nlinarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)]
  push_cast at hi
  calc y ^ (2 * i) * y ^ 2 * ((2 * i).factorial : ℝ)
      ≤ y ^ (2 * i) * 2 * ((2 * i).factorial : ℝ) := by gcongr
    _ ≤ y ^ (2 * i) * (((2 * i : ℝ) + 1 + 1) * ((2 * i : ℝ) + 1)) * ((2 * i).factorial : ℝ) := by
        gcongr
    _ = _ := by ring

lemma sinTerm_antitone {y : ℝ} (hy0 : 0 ≤ y) (hy : y ^ 2 ≤ 6) : Antitone (sinTerm y) := by
  refine antitone_nat_of_succ_le (fun i => ?_)
  unfold sinTerm
  have h1 : (2 * (i + 1) + 1) = ((2 * i + 1) + 1) + 1 := by ring
  rw [h1, Nat.factorial_succ, Nat.factorial_succ]
  have hf : (0 : ℝ) < ((2 * i + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hp : (0 : ℝ) ≤ y ^ (2 * i + 1) := by positivity
  have hf2 : (0 : ℝ) < (((2 * i + 1 + 1 + 1) * ((2 * i + 1 + 1) * (2 * i + 1).factorial) : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (Nat.factorial_pos _))
  rw [div_le_div_iff₀ hf2 hf]
  push_cast
  have : y ^ (2 * i + 1 + 1 + 1) = y ^ (2 * i + 1) * y ^ 2 := by ring
  rw [this]
  calc y ^ (2 * i + 1) * y ^ 2 * ((2 * i + 1).factorial : ℝ)
      ≤ y ^ (2 * i + 1) * 6 * ((2 * i + 1).factorial : ℝ) := by gcongr
    _ ≤ y ^ (2 * i + 1) * (((2 * i : ℝ) + 1 + 1 + 1) * ((2 * i : ℝ) + 1 + 1)) *
          ((2 * i + 1).factorial : ℝ) := by
        gcongr
        nlinarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)]
    _ = _ := by ring

lemma tendsto_cos_partial (y : ℝ) :
    Filter.Tendsto (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i * cosTerm y i) Filter.atTop
      (nhds (Real.cos y)) := by
  have h := (Real.hasSum_cos y).tendsto_sum_nat
  refine h.congr (fun n => ?_)
  refine Finset.sum_congr rfl (fun i _ => ?_)
  unfold cosTerm; ring

lemma tendsto_sin_partial (y : ℝ) :
    Filter.Tendsto (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i * sinTerm y i) Filter.atTop
      (nhds (Real.sin y)) := by
  have h := (Real.hasSum_sin y).tendsto_sum_nat
  refine h.congr (fun n => ?_)
  refine Finset.sum_congr rfl (fun i _ => ?_)
  unfold sinTerm; ring

theorem cos_ge_partial {y : ℝ} (hy : y ^ 2 ≤ 2) (N : ℕ) :
    ∑ i ∈ range (2 * N), (-1 : ℝ) ^ i * cosTerm y i ≤ Real.cos y :=
  (cosTerm_antitone hy).alternating_series_le_tendsto (tendsto_cos_partial y) N

theorem cos_le_partial {y : ℝ} (hy : y ^ 2 ≤ 2) (N : ℕ) :
    Real.cos y ≤ ∑ i ∈ range (2 * N + 1), (-1 : ℝ) ^ i * cosTerm y i :=
  (cosTerm_antitone hy).tendsto_le_alternating_series (tendsto_cos_partial y) N

theorem sin_ge_partial {y : ℝ} (hy0 : 0 ≤ y) (hy : y ^ 2 ≤ 6) (N : ℕ) :
    ∑ i ∈ range (2 * N), (-1 : ℝ) ^ i * sinTerm y i ≤ Real.sin y :=
  (sinTerm_antitone hy0 hy).alternating_series_le_tendsto (tendsto_sin_partial y) N

theorem sin_le_partial {y : ℝ} (hy0 : 0 ≤ y) (hy : y ^ 2 ≤ 6) (N : ℕ) :
    Real.sin y ≤ ∑ i ∈ range (2 * N + 1), (-1 : ℝ) ^ i * sinTerm y i :=
  (sinTerm_antitone hy0 hy).tendsto_le_alternating_series (tendsto_sin_partial y) N

end CirclePacking
