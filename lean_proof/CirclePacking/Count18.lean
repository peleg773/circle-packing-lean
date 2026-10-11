import Mathlib

/-!
# At most eleven unit circles touch a container smaller than the 19-circle container

If `B` centres lie on the circle of radius `ρ < 1/sin(π/12)` (`= ρ₁₉ = √6 + √2`), pairwise at distance at least
`2`, then `B ≤ 11`.  The angular distance (in turns, around the circle) of two such centres exceeds `1/12`; the
sorted angles split one turn into `B` gaps, each larger than `1/12`.
-/

open Real

namespace CirclePacking

/-- `cos (2π t) ≥ cos (π/6)` when `t` is within `1/12` of an integer -/
lemma cos_two_pi_ge_of_near {t : ℝ} (h : |t| ≤ 1 / 12) : cos (π / 6) ≤ cos (2 * π * t) := by
  rw [← cos_abs (2 * π * t), abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  apply cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith [pi_pos])
  nlinarith [pi_pos]

/-- two centres on the circle of radius `ρ < 1/sin(π/12)` at distance `≥ 2` differ by more than `1/12` turn,
measured in `[0, 1)`: both the difference of the fractional parts and its complement exceed `1/12` -/
lemma sep_of_dist {ρ x y : ℝ} (hρ : 0 < ρ) (hρ19 : ρ < 1 / sin (π / 12))
    (h : 4 ≤ 2 * ρ ^ 2 - 2 * ρ ^ 2 * cos (2 * π * (x - y))) (hxy : y ≤ x) (hx1 : x - y < 1) :
    1 / 12 < x - y ∧ 1 / 12 < 1 - (x - y) := by
  have hs : 0 < sin (π / 12) := sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [pi_pos])
  -- `cos (2π(x - y)) ≤ 1 - 2/ρ² < cos (π/6)`
  have hρs : ρ * sin (π / 12) < 1 := by rwa [lt_div_iff₀ hs] at hρ19
  have hc6 : cos (π / 6) = 1 - 2 * sin (π / 12) ^ 2 := by
    rw [show π / 6 = 2 * (π / 12) by ring, cos_two_mul, ← sin_sq_add_cos_sq (π / 12)]; ring
  have hcos : cos (2 * π * (x - y)) < cos (π / 6) := by
    have hρ2 : 0 < ρ ^ 2 := by positivity
    have h1 : ρ ^ 2 * cos (2 * π * (x - y)) ≤ ρ ^ 2 - 2 := by linarith
    have h2 : ρ ^ 2 * sin (π / 12) ^ 2 < 1 := by nlinarith [mul_pos hρ hs]
    rw [hc6]
    by_contra hge
    push Not at hge
    nlinarith
  constructor
  · by_contra hle
    push Not at hle
    have := cos_two_pi_ge_of_near (t := x - y) (by rw [abs_le]; constructor <;> linarith)
    linarith
  · by_contra hle
    push Not at hle
    have e : cos (2 * π * (x - y)) = cos (2 * π * (x - y - 1)) := by
      rw [show 2 * π * (x - y - 1) = 2 * π * (x - y) - 2 * π by ring, cos_sub_two_pi]
    have := cos_two_pi_ge_of_near (t := x - y - 1) (by rw [abs_le]; constructor <;> linarith)
    linarith

/-- **At most eleven boundary circles below `ρ₁₉`.** -/
theorem card_le_eleven {ρ : ℝ} (hρ : 0 < ρ) (hρ19 : ρ < 1 / sin (π / 12)) {B : ℕ} (a : Fin B → ℝ)
    (hbb : ∀ b b', b ≠ b' → 4 ≤ 2 * ρ ^ 2 - 2 * ρ ^ 2 * cos (2 * π * (a b - a b'))) : B ≤ 11 := by
  by_contra hB
  push Not at hB
  -- fractional parts, sorted
  set x : Fin B → ℝ := fun b => Int.fract (a b) with hx
  have hcos : ∀ b b', cos (2 * π * (a b - a b')) = cos (2 * π * (x b - x b')) := by
    intro b b'
    have e : a b - a b' = (x b - x b') + ((⌊a b⌋ - ⌊a b'⌋ : ℤ) : ℝ) := by
      simp only [hx, Int.fract]; push_cast; ring
    rw [e, mul_add, show 2 * π * ((⌊a b⌋ - ⌊a b'⌋ : ℤ) : ℝ) = ((⌊a b⌋ - ⌊a b'⌋ : ℤ) : ℝ) * (2 * π) by ring,
      cos_add_int_mul_two_pi]
  have hx01 : ∀ b, 0 ≤ x b ∧ x b < 1 := fun b => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  set σ := Tuple.sort x with hσ
  set y : Fin B → ℝ := x ∘ σ with hy
  have hmono : Monotone y := Tuple.monotone_sort x
  have hsep : ∀ i j : Fin B, i < j → 1 / 12 < y j - y i ∧ 1 / 12 < 1 - (y j - y i) := by
    intro i j hij
    have hne : σ j ≠ σ i := fun e => (ne_of_gt hij) (σ.injective e)
    have h := hbb (σ j) (σ i) hne
    rw [hcos] at h
    have e1 : y j = x (σ j) := rfl
    have e2 : y i = x (σ i) := rfl
    rw [e1, e2]
    exact sep_of_dist hρ hρ19 h (by rw [← e1, ← e2]; exact hmono hij.le)
      (by linarith [(hx01 (σ j)).2, (hx01 (σ i)).1])
  -- the gaps between consecutive sorted angles exceed `1/12`, and so does the wrap-around gap
  have hB0 : 0 < B := by omega
  set first : Fin B := ⟨0, hB0⟩
  set last : Fin B := ⟨B - 1, by omega⟩
  have hstep : ∀ m : ℕ, (hm : m < B - 1) → (m + 1 : ℝ) / 12 < y ⟨m + 1, by omega⟩ - y first := by
    intro m hm
    induction m with
    | zero =>
      have := (hsep first ⟨1, by omega⟩ (by simp [first, Fin.lt_def])).1
      push_cast; linarith
    | succ m ih =>
      have h1 := ih (by omega)
      have h2 := (hsep ⟨m + 1, by omega⟩ ⟨m + 2, by omega⟩ (by simp [Fin.lt_def])).1
      push_cast at h1 ⊢
      linarith
  have hspan := hstep (B - 2) (by omega)
  have hlast : (⟨B - 2 + 1, by omega⟩ : Fin B) = last := by simp only [last]; congr 1; omega
  rw [hlast] at hspan
  have hwrap := (hsep first last (by simp only [first, last, Fin.lt_def]; omega)).2
  have hBr : (12 : ℝ) ≤ B := by exact_mod_cast hB
  have : ((B - 2 : ℕ) : ℝ) = (B : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  rw [this] at hspan
  linarith

end CirclePacking
