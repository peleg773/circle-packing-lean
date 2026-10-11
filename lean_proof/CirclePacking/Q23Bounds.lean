import CirclePacking.Q23

/-!
# Rational bounds for `ℚ(√2, √3)`

`lo23 x ≤ x.eval ≤ hi23 x`, from `rl2 ≤ √2 ≤ rh2` and `rl3' ≤ √3 ≤ rh3'` (width `2⁻¹⁷⁰`), and `√6 = √2 √3`.
-/

namespace CirclePacking

def rl2 : ℚ := 2116480447430499751252734943246140439044294856528969 / 2 ^ 170
def rh2 : ℚ := 2116480447430499751252734943246140439044294856528970 / 2 ^ 170
def rl3' : ℚ := 2592148573391080265158740781003200204284289852059983 / 2 ^ 170
def rh3' : ℚ := 2592148573391080265158740781003200204284289852059984 / 2 ^ 170

theorem rl2_ok : 0 ≤ rl2 ∧ rl2 ^ 2 ≤ 2 := by decide +kernel
theorem rh2_ok : 0 ≤ rh2 ∧ 2 ≤ rh2 ^ 2 := by decide +kernel
theorem rl3'_ok : 0 ≤ rl3' ∧ rl3' ^ 2 ≤ 3 := by decide +kernel
theorem rh3'_ok : 0 ≤ rh3' ∧ 3 ≤ rh3' ^ 2 := by decide +kernel

lemma sqrt_bounds_of {q l h : ℚ} (hl : 0 ≤ l ∧ l ^ 2 ≤ q) (hh : 0 ≤ h ∧ q ≤ h ^ 2) :
    ((l : ℚ) : ℝ) ≤ √(q : ℝ) ∧ √(q : ℝ) ≤ ((h : ℚ) : ℝ) := by
  have l0 : (0 : ℝ) ≤ l := by exact_mod_cast hl.1
  have h0 : (0 : ℝ) ≤ h := by exact_mod_cast hh.1
  have l2 : (l : ℝ) ^ 2 ≤ q := by exact_mod_cast hl.2
  have h2 : (q : ℝ) ≤ (h : ℝ) ^ 2 := by exact_mod_cast hh.2
  constructor
  · calc ((l : ℚ) : ℝ) = √((l : ℝ) ^ 2) := (Real.sqrt_sq l0).symm
      _ ≤ √(q : ℝ) := Real.sqrt_le_sqrt l2
  · calc √(q : ℝ) ≤ √((h : ℝ) ^ 2) := Real.sqrt_le_sqrt h2
      _ = h := Real.sqrt_sq h0

lemma sqrt2_bounds : ((rl2 : ℚ) : ℝ) ≤ √2 ∧ √2 ≤ ((rh2 : ℚ) : ℝ) := by
  have := sqrt_bounds_of (q := 2) rl2_ok rh2_ok
  simpa using this

lemma sqrt3_bounds : ((rl3' : ℚ) : ℝ) ≤ √3 ∧ √3 ≤ ((rh3' : ℚ) : ℝ) := by
  have := sqrt_bounds_of (q := 3) rl3'_ok rh3'_ok
  simpa using this

/-- the interval of `c · t` for `t ∈ [l, h]` -/
def mlo (c l h : ℚ) : ℚ := min (c * l) (c * h)
def mhi (c l h : ℚ) : ℚ := max (c * l) (c * h)

lemma mlo_le {c l h : ℚ} {t : ℝ} (hl : (l : ℝ) ≤ t) (hh : t ≤ (h : ℝ)) : ((mlo c l h : ℚ) : ℝ) ≤ c * t := by
  simp only [mlo]; push_cast
  rcases le_total 0 (c : ℝ) with hc | hc
  · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hl hc)
  · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hh hc)

lemma le_mhi {c l h : ℚ} {t : ℝ} (hl : (l : ℝ) ≤ t) (hh : t ≤ (h : ℝ)) : c * t ≤ ((mhi c l h : ℚ) : ℝ) := by
  simp only [mhi]; push_cast
  rcases le_total 0 (c : ℝ) with hc | hc
  · exact (mul_le_mul_of_nonneg_left hh hc).trans (le_max_right _ _)
  · exact (mul_le_mul_of_nonpos_left hl hc).trans (le_max_left _ _)

def lo23 (x : Q23) : ℚ := x.a + mlo x.b rl2 rh2 + mlo x.c rl3' rh3' + mlo x.d (rl2 * rl3') (rh2 * rh3')
def hi23 (x : Q23) : ℚ := x.a + mhi x.b rl2 rh2 + mhi x.c rl3' rh3' + mhi x.d (rl2 * rl3') (rh2 * rh3')

lemma sqrt6_bounds : ((rl2 * rl3' : ℚ) : ℝ) ≤ √2 * √3 ∧ √2 * √3 ≤ ((rh2 * rh3' : ℚ) : ℝ) := by
  obtain ⟨a1, a2⟩ := sqrt2_bounds
  obtain ⟨b1, b2⟩ := sqrt3_bounds
  have l3 : (0 : ℝ) ≤ rl3' := by exact_mod_cast rl3'_ok.1
  push_cast
  constructor
  · exact mul_le_mul a1 b1 l3 (Real.sqrt_nonneg 2)
  · exact mul_le_mul a2 b2 (Real.sqrt_nonneg 3) (le_trans (Real.sqrt_nonneg 2) a2)

lemma lo23_le (x : Q23) : ((lo23 x : ℚ) : ℝ) ≤ x.eval := by
  obtain ⟨a1, a2⟩ := sqrt2_bounds
  obtain ⟨b1, b2⟩ := sqrt3_bounds
  obtain ⟨c1, c2⟩ := sqrt6_bounds
  have h1 := mlo_le (c := x.b) a1 a2
  have h2 := mlo_le (c := x.c) b1 b2
  have h3 := mlo_le (c := x.d) c1 c2
  simp only [lo23, Q23.eval]; push_cast at h1 h2 h3 ⊢
  linarith

lemma le_hi23 (x : Q23) : x.eval ≤ ((hi23 x : ℚ) : ℝ) := by
  obtain ⟨a1, a2⟩ := sqrt2_bounds
  obtain ⟨b1, b2⟩ := sqrt3_bounds
  obtain ⟨c1, c2⟩ := sqrt6_bounds
  have h1 := le_mhi (c := x.b) a1 a2
  have h2 := le_mhi (c := x.c) b1 b2
  have h3 := le_mhi (c := x.d) c1 c2
  simp only [hi23, Q23.eval]; push_cast at h1 h2 h3 ⊢
  linarith

end CirclePacking
