import CirclePacking.Canon

/-!
# Certified cosine and sine enclosures at integer angles; angle brackets from cross products

`cosLo t ≤ cos (2π t/S) ≤ cosHi t` and `sinLo t ≤ sin (2π t/S) ≤ sinHi t` for every integer `t` (units
`1/S` turns), from the certified lower bound `cosZ` and the symmetries of the cosine.  A point `z` whose
cross products with the directions at angles `t₁ ≤ t₂` (with `t₂ - t₁ ≤ 1/2`) are strictly positive has its
angle (in turns, modulo 1) strictly between `t₁` and `t₂`.
-/

open Real

namespace CirclePacking

/-- certified lower bound of `cos (2π t/S)` (units `1/S`), any integer `t` -/
def cosLo (t : Int) : Int := if 2 * (t % S) ≤ S then cosZ (t % S) else cosZ (S - t % S)
/-- certified upper bound of `cos (2π t/S)` (units `1/S`), any integer `t` -/
def cosHi (t : Int) : Int := if 2 * (t % S) ≤ S then -cosZ (S / 2 - t % S) else -cosZ (t % S - S / 2)
/-- certified bounds of `sin (2π t/S) = cos (2π (t - S/4)/S)` -/
def sinLo (t : Int) : Int := cosLo (t - S / 4)
def sinHi (t : Int) : Int := cosHi (t - S / 4)

lemma S_div_two : S / 2 * 2 = S := by decide
lemma S_div_four : S / 4 * 4 = S := by decide

lemma sc_S_div_two : sc (S / 2) = 1 / 2 := by
  have h : ((S / 2 : ℤ) : ℝ) * 2 = (S : ℝ) := by exact_mod_cast S_div_two
  have hS := S_pos
  unfold sc; field_simp; linarith

lemma sc_S_div_four : sc (S / 4) = 1 / 4 := by
  have h : ((S / 4 : ℤ) : ℝ) * 4 = (S : ℝ) := by exact_mod_cast S_div_four
  have hS := S_pos
  unfold sc; field_simp; linarith

/-- reduction modulo one turn -/
lemma cos_sc_emod (t : ℤ) : Real.cos (2 * π * sc t) = Real.cos (2 * π * sc (t % S)) := by
  have hS : (0 : ℤ) < S := by decide
  have e : t = t % S + S * (t / S) := (Int.emod_add_mul_ediv t S).symm
  conv_lhs => rw [e]
  rw [sc_add, show S * (t / S) = (t / S) * S by ring, show sc ((t / S) * S) = ((t / S : ℤ) : ℝ) by
    unfold sc; have := S_pos; push_cast; field_simp]
  rw [show 2 * π * (sc (t % S) + ((t / S : ℤ) : ℝ)) = 2 * π * sc (t % S) + ((t / S : ℤ) : ℝ) * (2 * π) by ring,
    Real.cos_add_int_mul_two_pi]

lemma emod_bounds (t : ℤ) : 0 ≤ t % S ∧ t % S < S := by
  have hS : (0 : ℤ) < S := by decide
  exact ⟨Int.emod_nonneg t hS.ne', Int.emod_lt_of_pos t hS⟩

lemma cosLo_le (t : ℤ) : sc (cosLo t) ≤ Real.cos (2 * π * sc t) := by
  rw [cos_sc_emod]
  obtain ⟨h0, h1⟩ := emod_bounds t
  unfold cosLo
  split_ifs with h
  · exact cosZ_sc h0 h
  · have e : Real.cos (2 * π * sc (t % S)) = Real.cos (2 * π * sc (S - t % S)) := by
      rw [sc_sub, sc_S, show 2 * π * (1 - sc (t % S)) = -(2 * π * sc (t % S)) + 1 * (2 * π) by ring,
        show (1 : ℝ) * (2 * π) = ((1 : ℤ) : ℝ) * (2 * π) by push_cast; ring, Real.cos_add_int_mul_two_pi,
        Real.cos_neg]
    rw [e]
    exact cosZ_sc (by omega) (by omega)

lemma cos_le_cosHi (t : ℤ) : Real.cos (2 * π * sc t) ≤ sc (cosHi t) := by
  rw [cos_sc_emod]
  obtain ⟨h0, h1⟩ := emod_bounds t
  have h2 := S_div_two
  unfold cosHi
  split_ifs with h
  · have e : Real.cos (2 * π * sc (t % S)) = -Real.cos (2 * π * sc (S / 2 - t % S)) := by
      rw [sc_sub, sc_S_div_two, show 2 * π * (1 / 2 - sc (t % S)) = π - 2 * π * sc (t % S) by ring,
        Real.cos_pi_sub, neg_neg]
    rw [e, show sc (-cosZ (S / 2 - t % S)) = -sc (cosZ (S / 2 - t % S)) by unfold sc; push_cast; ring]
    have := cosZ_sc (D := S / 2 - t % S) (by omega) (by omega)
    linarith
  · have e : Real.cos (2 * π * sc (t % S)) = -Real.cos (2 * π * sc (t % S - S / 2)) := by
      rw [sc_sub, sc_S_div_two, show 2 * π * (sc (t % S) - 1 / 2) = 2 * π * sc (t % S) - π by ring,
        Real.cos_sub_pi, neg_neg]
    rw [e, show sc (-cosZ (t % S - S / 2)) = -sc (cosZ (t % S - S / 2)) by unfold sc; push_cast; ring]
    have := cosZ_sc (D := t % S - S / 2) (by omega) (by omega)
    linarith

lemma sin_eq_cos_shift (t : ℤ) : Real.sin (2 * π * sc t) = Real.cos (2 * π * sc (t - S / 4)) := by
  rw [sc_sub, sc_S_div_four, show 2 * π * (sc t - 1 / 4) = 2 * π * sc t - π / 2 by ring, Real.cos_sub_pi_div_two]

lemma sinLo_le (t : ℤ) : sc (sinLo t) ≤ Real.sin (2 * π * sc t) := by
  rw [sin_eq_cos_shift]; exact cosLo_le _

lemma sin_le_sinHi (t : ℤ) : Real.sin (2 * π * sc t) ≤ sc (sinHi t) := by
  rw [sin_eq_cos_shift]; exact cos_le_cosHi _

/-! ### Angle brackets -/

lemma pos_sin_fract {x : ℝ} (h : 0 < Real.sin (2 * π * x)) : 0 < Int.fract x ∧ Int.fract x < 1 / 2 := by
  have e : Real.sin (2 * π * x) = Real.sin (2 * π * Int.fract x) := by
    rw [show 2 * π * x = 2 * π * Int.fract x + ((⌊x⌋ : ℤ) : ℝ) * (2 * π) by
      rw [Int.fract]; push_cast; ring, Real.sin_add_int_mul_two_pi]
  rw [e] at h
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  constructor
  · rcases h0.lt_or_eq with h0 | h0
    · exact h0
    · rw [← h0, mul_zero, Real.sin_zero] at h; exact absurd h (lt_irrefl 0)
  · by_contra hc
    push Not at hc
    have : Real.sin (2 * π * Int.fract x) ≤ 0 := by
      have e2 : 2 * π * Int.fract x = (2 * π * Int.fract x - 2 * π) + 2 * π := by ring
      rw [e2, Real.sin_add_two_pi]
      apply Real.sin_nonpos_of_nonpos_of_neg_pi_le
      · nlinarith [Real.pi_pos]
      · nlinarith [Real.pi_pos]
    linarith

/-- **Angle bracket from cross products.** -/
lemma angle_bracket {z : ℂ} {t1 t2 : ℝ} (h12 : t1 ≤ t2) (h12' : t2 - t1 ≤ 1 / 2)
    (h1 : 0 < Real.cos (2 * π * t1) * z.im - Real.sin (2 * π * t1) * z.re)
    (h2 : 0 < z.re * Real.sin (2 * π * t2) - z.im * Real.cos (2 * π * t2)) :
    ∃ m : ℤ, t1 < toTurn z + m ∧ toTurn z + m < t2 := by
  set φ := toTurn z
  have hz : z = polar ‖z‖ φ := (polar_toTurn z).symm
  have hre : z.re = ‖z‖ * Real.cos (2 * π * φ) := (congrArg Complex.re hz).trans rfl
  have him : z.im = ‖z‖ * Real.sin (2 * π * φ) := (congrArg Complex.im hz).trans rfl
  have hn : 0 ≤ ‖z‖ := norm_nonneg _
  have s1 : 0 < ‖z‖ * Real.sin (2 * π * (φ - t1)) := by
    rw [show 2 * π * (φ - t1) = 2 * π * φ - 2 * π * t1 by ring, Real.sin_sub]
    rw [hre, him] at h1; nlinarith
  have s2 : 0 < ‖z‖ * Real.sin (2 * π * (t2 - φ)) := by
    rw [show 2 * π * (t2 - φ) = 2 * π * t2 - 2 * π * φ by ring, Real.sin_sub]
    rw [hre, him] at h2; nlinarith
  have hzn : 0 < ‖z‖ := by
    rcases hn.lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at s1; exact absurd s1 (lt_irrefl 0)
  have sin1 : 0 < Real.sin (2 * π * (φ - t1)) := pos_of_mul_pos_right s1 hn
  have sin2 : 0 < Real.sin (2 * π * (t2 - φ)) := pos_of_mul_pos_right s2 hn
  obtain ⟨a0, a1⟩ := pos_sin_fract sin1
  obtain ⟨b0, b1⟩ := pos_sin_fract sin2
  -- `fract (φ - t1) + fract (t2 - φ) = t2 - t1`
  set k1 := ⌊φ - t1⌋
  set k2 := ⌊t2 - φ⌋
  have ha : Int.fract (φ - t1) = φ - t1 - k1 := rfl
  have hb : Int.fract (t2 - φ) = t2 - φ - k2 := rfl
  have hk : (k1 + k2 : ℤ) = 0 := by
    have hsum : ((k1 + k2 : ℤ) : ℝ) = (t2 - t1) - (Int.fract (φ - t1) + Int.fract (t2 - φ)) := by
      rw [ha, hb]; push_cast; ring
    have hlo : (-1 : ℝ) < ((k1 + k2 : ℤ) : ℝ) := by rw [hsum]; linarith
    have hhi : ((k1 + k2 : ℤ) : ℝ) < 1 := by rw [hsum]; linarith
    have hlo' : -1 < k1 + k2 := by exact_mod_cast hlo
    have hhi' : k1 + k2 < 1 := by exact_mod_cast hhi
    omega
  refine ⟨-k1, ?_, ?_⟩
  · push_cast; linarith
  · have hk' : ((k2 : ℤ) : ℝ) = -((k1 : ℤ) : ℝ) := by
      have : ((k1 + k2 : ℤ) : ℝ) = 0 := by exact_mod_cast hk
      push_cast at this; linarith
    push_cast
    have : Int.fract (φ - t1) + Int.fract (t2 - φ) = t2 - t1 := by rw [ha, hb, hk']; ring
    linarith

end CirclePacking
