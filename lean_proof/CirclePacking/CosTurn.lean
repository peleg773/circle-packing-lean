import CirclePacking.Trig
import Mathlib.Analysis.Real.Pi.Bounds
import C15Compute

/-!
# Correctness of the certified cosine bound `cosZ`

`cosZ D / 2^40 ≤ cos (2π D / 2^40)` for `0 ≤ D ≤ 2^39`.
-/

open Real

set_option exponentiation.threshold 2000

namespace CirclePacking

lemma piLo_lt_pi : (piLo : ℝ) < π := by
  have := Real.pi_gt_d20
  unfold piLo; push_cast; norm_num at this ⊢; linarith

lemma pi_lt_piHi : π < (piHi : ℝ) := by
  have := Real.pi_lt_d20
  unfold piHi; push_cast; norm_num at this ⊢; linarith

lemma cosL8_le {y : ℚ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : ((cosL8 y : ℚ) : ℝ) ≤ Real.cos y := by
  have hy : ((y : ℝ)) ^ 2 ≤ 2 := by
    have : (y : ℝ) ≤ 1 := by exact_mod_cast h1
    have : (0 : ℝ) ≤ y := by exact_mod_cast h0
    nlinarith
  have h := cos_ge_partial hy 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cosTerm] at h
  norm_num [Nat.factorial] at h
  unfold cosL8; push_cast
  linarith

lemma cos_le_cosU7 {y : ℚ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : Real.cos y ≤ ((cosU7 y : ℚ) : ℝ) := by
  have hy : ((y : ℝ)) ^ 2 ≤ 2 := by
    have : (y : ℝ) ≤ 1 := by exact_mod_cast h1
    have : (0 : ℝ) ≤ y := by exact_mod_cast h0
    nlinarith
  have h := cos_le_partial hy 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cosTerm] at h
  norm_num [Nat.factorial] at h
  unfold cosU7; push_cast
  linarith

lemma sinL8_le {y : ℚ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : ((sinL8 y : ℚ) : ℝ) ≤ Real.sin y := by
  have h0' : (0 : ℝ) ≤ y := by exact_mod_cast h0
  have hy : ((y : ℝ)) ^ 2 ≤ 6 := by
    have : (y : ℝ) ≤ 1 := by exact_mod_cast h1
    nlinarith
  have h := sin_ge_partial h0' hy 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, sinTerm] at h
  norm_num [Nat.factorial] at h
  unfold sinL8; push_cast
  linarith

lemma sin_le_sinU7 {y : ℚ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : Real.sin y ≤ ((sinU7 y : ℚ) : ℝ) := by
  have h0' : (0 : ℝ) ≤ y := by exact_mod_cast h0
  have hy : ((y : ℝ)) ^ 2 ≤ 6 := by
    have : (y : ℝ) ≤ 1 := by exact_mod_cast h1
    nlinarith
  have h := sin_le_partial h0' hy 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, sinTerm] at h
  norm_num [Nat.factorial] at h
  unfold sinU7; push_cast
  linarith

/-! ### The integer forms of the partial sums -/

lemma cosL8Num_eq (Y : ℤ) :
    ((cosL8Num Y : ℤ) : ℚ) = cosL8 ((Y : ℚ) / 2 ^ 40) * (2 ^ 560 * 87178291200) := by
  simp only [cosL8Num, cosL8, cL8K0, cL8K1, cL8K2, cL8K3, cL8K4, cL8K5, cL8K6]
  push_cast
  ring

lemma cosU7Num_eq (Y : ℤ) :
    ((cosU7Num Y : ℤ) : ℚ) = cosU7 ((Y : ℚ) / 2 ^ 40) * (2 ^ 480 * 479001600) := by
  simp only [cosU7Num, cosU7, cU7K0, cU7K1, cU7K2, cU7K3, cU7K4, cU7K5]
  push_cast
  ring

lemma sinL8Num_eq (Y : ℤ) :
    ((sinL8Num Y : ℤ) : ℚ) = sinL8 ((Y : ℚ) / 2 ^ 40) * (2 ^ 600 * 1307674368000) := by
  simp only [sinL8Num, sinL8, sL8K0, sL8K1, sL8K2, sL8K3, sL8K4, sL8K5, sL8K6]
  push_cast
  ring

lemma sinU7Num_eq (Y : ℤ) :
    ((sinU7Num Y : ℤ) : ℚ) = sinU7 ((Y : ℚ) / 2 ^ 40) * (2 ^ 520 * 6227020800) := by
  simp only [sinU7Num, sinU7, sU7K0, sU7K1, sU7K2, sU7K3, sU7K4, sU7K5]
  push_cast
  ring

/-! ### Integer division facts -/

lemma ediv_le_div (a b : ℤ) (hb : 0 < b) : (((a / b : ℤ)) : ℝ) ≤ (a : ℝ) / b := by
  have h := Int.ediv_mul_le a (ne_of_gt hb)
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [le_div_iff₀ hb']
  exact_mod_cast h

lemma div_lt_ediv_add_one (a b : ℤ) (hb : 0 < b) : (a : ℝ) / b < (((a / b : ℤ)) : ℝ) + 1 := by
  have h := Int.lt_ediv_add_one_mul_self a hb
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_lt_iff₀ hb']
  exact_mod_cast h

lemma div_le_ceilDiv (a b : ℤ) (hb : 0 < b) : (a : ℝ) / b ≤ ((ceilDiv a b : ℤ) : ℝ) := by
  unfold ceilDiv
  have h := ediv_le_div (-a) b hb
  push_cast at h ⊢
  rw [neg_div] at h
  linarith

lemma ceilDiv_lt (a b : ℤ) (hb : 0 < b) : ((ceilDiv a b : ℤ) : ℝ) < (a : ℝ) / b + 1 := by
  unfold ceilDiv
  have h := div_lt_ediv_add_one (-a) b hb
  push_cast at h ⊢
  rw [neg_div] at h
  linarith

/-! ### The constants -/

lemma S_eq : (S : ℤ) = 2 ^ 40 := by norm_num [S]

lemma S_pos : (0 : ℝ) < (S : ℝ) := by rw [S_eq]; norm_num

lemma twoPiHi60_ge : 2 * π * 2 ^ 60 ≤ (twoPiHi60 : ℝ) := by
  have h := pi_lt_piHi
  have : (2 * (piHi : ℝ) * 2 ^ 60) ≤ (twoPiHi60 : ℝ) := by
    unfold piHi twoPiHi60; push_cast; norm_num
  nlinarith

lemma twoPiLo60_le : (twoPiLo60 : ℝ) ≤ 2 * π * 2 ^ 60 := by
  have h := piLo_lt_pi
  have : (twoPiLo60 : ℝ) ≤ (2 * (piLo : ℝ) * 2 ^ 60) := by
    unfold piLo twoPiLo60; push_cast; norm_num
  nlinarith

lemma twoPiHi60_le : (twoPiHi60 : ℝ) ≤ 63 / 10 * 2 ^ 60 := by
  unfold twoPiHi60; norm_num

/-- generic step: `⌊N / D⌋ / 2^40 ≤ p` when `N = p * D * 2^40` -/
lemma floor_scaled_le {N D : ℤ} {p : ℚ} (hD : 0 < D) (hN : (N : ℚ) = p * (D * 2 ^ 40)) :
    ((N / D : ℤ) : ℝ) / 2 ^ 40 ≤ (p : ℝ) := by
  have h := ediv_le_div N D hD
  have hN' : (N : ℝ) = (p : ℝ) * (D * 2 ^ 40) := by exact_mod_cast hN
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  rw [div_le_iff₀ (by norm_num)]
  calc ((N / D : ℤ) : ℝ) ≤ (N : ℝ) / D := h
    _ = (p : ℝ) * 2 ^ 40 := by rw [hN']; field_simp

/-- generic step: `p ≤ ⌈N / D⌉ / 2^40` when `N = p * D * 2^40` -/
lemma le_ceil_scaled {N D : ℤ} {p : ℚ} (hD : 0 < D) (hN : (N : ℚ) = p * (D * 2 ^ 40)) :
    (p : ℝ) ≤ ((ceilDiv N D : ℤ) : ℝ) / 2 ^ 40 := by
  have h := div_le_ceilDiv N D hD
  have hN' : (N : ℝ) = (p : ℝ) * (D * 2 ^ 40) := by exact_mod_cast hN
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  rw [le_div_iff₀ (by norm_num)]
  calc (p : ℝ) * 2 ^ 40 = (N : ℝ) / D := by rw [hN']; field_simp
    _ ≤ _ := h

theorem cosZ_le (D : ℤ) (h0 : 0 ≤ D) (h1 : 2 * D ≤ S) :
    ((cosZ D : ℤ) : ℝ) / S ≤ Real.cos (2 * π * ((D : ℝ) / S)) := by
  have hS : (S : ℝ) = 2 ^ 40 := by rw [S_eq]; norm_num
  have hSZ : S = 2 ^ 40 := S_eq
  have hpi3 : (3 : ℝ) < π := Real.pi_gt_three
  have hpi4 : π < 4 := Real.pi_lt_four
  have hH := twoPiHi60_ge
  have hL := twoPiLo60_le
  have hH2 := twoPiHi60_le
  have hD0 : (0 : ℝ) ≤ D := by exact_mod_cast h0
  have hD1 : 2 * (D : ℝ) ≤ 2 ^ 40 := by
    have : ((2 * D : ℤ) : ℝ) ≤ ((S : ℤ) : ℝ) := by exact_mod_cast h1
    push_cast at this; rw [hS] at this; exact this
  rw [hS]
  unfold cosZ
  split_ifs with c1 c2 c3
  · -- case 1: 8D ≤ S
    have c1' : 8 * (D : ℝ) ≤ 2 ^ 40 := by
      have : ((8 * D : ℤ) : ℝ) ≤ ((S : ℤ) : ℝ) := by exact_mod_cast c1
      push_cast at this; rw [hS] at this; exact this
    set Y := ceilDiv (twoPiHi60 * D) two60 with hY
    have hY1 : ((twoPiHi60 * D : ℤ) : ℝ) / (two60 : ℤ) ≤ (Y : ℝ) :=
      div_le_ceilDiv _ _ (by norm_num [two60])
    have hY2 : (Y : ℝ) < ((twoPiHi60 * D : ℤ) : ℝ) / (two60 : ℤ) + 1 :=
      ceilDiv_lt _ _ (by norm_num [two60])
    push_cast [two60] at hY1 hY2
    have hYge : 2 * π * ((D : ℝ) / 2 ^ 40) ≤ (Y : ℝ) / 2 ^ 40 := by
      have h2 : 2 * π * (D : ℝ) ≤ (twoPiHi60 : ℝ) * D / 2 ^ 60 := by
        rw [le_div_iff₀ (by norm_num)]; nlinarith
      rw [show 2 * π * ((D : ℝ) / 2 ^ 40) = (2 * π * D) / 2 ^ 40 by ring]
      exact div_le_div_of_nonneg_right (by linarith) (by norm_num)
    have hYle : (Y : ℝ) / 2 ^ 40 ≤ 1 := by
      rw [div_le_one (by norm_num)]
      have : (twoPiHi60 : ℝ) * D / 2 ^ 60 ≤ 63 / 10 * D := by
        rw [div_le_iff₀ (by norm_num)]; nlinarith
      nlinarith
    have hY0 : (0 : ℝ) ≤ (Y : ℝ) / 2 ^ 40 := le_trans (by positivity) hYge
    -- the rational argument
    set y : ℚ := (Y : ℚ) / 2 ^ 40 with hy
    have hyR : ((y : ℚ) : ℝ) = (Y : ℝ) / 2 ^ 40 := by rw [hy]; push_cast; ring
    have hy0 : (0 : ℚ) ≤ y := by
      have : (0 : ℝ) ≤ ((y : ℚ) : ℝ) := by rw [hyR]; exact hY0
      exact_mod_cast this
    have hy1 : y ≤ 1 := by
      have : ((y : ℚ) : ℝ) ≤ 1 := by rw [hyR]; exact hYle
      exact_mod_cast this
    have hcos := cosL8_le hy0 hy1
    rw [hyR] at hcos
    have hmono : Real.cos ((Y : ℝ) / 2 ^ 40) ≤ Real.cos (2 * π * ((D : ℝ) / 2 ^ 40)) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith) hYge
    have hfl : ((cosL8Num Y / cDenL8 : ℤ) : ℝ) / 2 ^ 40 ≤ ((cosL8 y : ℚ) : ℝ) := by
      apply floor_scaled_le (by norm_num [cDenL8])
      rw [cosL8Num_eq, hy]; unfold cDenL8; push_cast; ring
    linarith
  · -- case 2: S < 8D, 4D ≤ S;  cos(2π d) = sin(2π (1/4 - d))
    have c1' : (2 : ℝ) ^ 40 < 8 * (D : ℝ) := by
      have : ((S : ℤ) : ℝ) < ((8 * D : ℤ) : ℝ) := by exact_mod_cast not_le.mp c1
      push_cast at this; rw [hS] at this; exact this
    have c2' : 4 * (D : ℝ) ≤ 2 ^ 40 := by
      have : ((4 * D : ℤ) : ℝ) ≤ ((S : ℤ) : ℝ) := by exact_mod_cast c2
      push_cast at this; rw [hS] at this; exact this
    set Y := (twoPiLo60 * (S - 4 * D)) / (4 * two60) with hY
    have hY1 : (Y : ℝ) ≤ ((twoPiLo60 * (S - 4 * D) : ℤ) : ℝ) / ((4 * two60 : ℤ) : ℝ) :=
      ediv_le_div _ _ (by norm_num [two60])
    have hY2 : ((twoPiLo60 * (S - 4 * D) : ℤ) : ℝ) / ((4 * two60 : ℤ) : ℝ) < (Y : ℝ) + 1 :=
      div_lt_ediv_add_one _ _ (by norm_num [two60])
    push_cast [two60] at hY1 hY2
    rw [hS] at hY1 hY2
    have hnum0 : (0 : ℝ) ≤ (twoPiLo60 : ℝ) * (2 ^ 40 - 4 * D) := by
      apply mul_nonneg (by unfold twoPiLo60; norm_num) (by linarith)
    have hY0' : (0 : ℝ) ≤ (Y : ℝ) := by
      have : (0 : ℝ) ≤ (twoPiLo60 : ℝ) * (2 ^ 40 - 4 * D) / (4 * 2 ^ 60) := by positivity
      have hint : (-1 : ℤ) < Y := by
        have : (-1 : ℝ) < (Y : ℝ) := by linarith
        exact_mod_cast this
      have : (0 : ℤ) ≤ Y := by omega
      exact_mod_cast this
    set e : ℝ := 1 / 4 - (D : ℝ) / 2 ^ 40 with he
    have he0 : 0 ≤ e := by
      have : (D : ℝ) / 2 ^ 40 ≤ 1 / 4 := by rw [div_le_iff₀ (by norm_num)]; linarith
      rw [he]; linarith
    have he1 : e ≤ 1 / 8 := by
      have : (1 : ℝ) / 8 ≤ (D : ℝ) / 2 ^ 40 := by rw [le_div_iff₀ (by norm_num)]; linarith
      rw [he]; linarith
    have hYle : (Y : ℝ) / 2 ^ 40 ≤ 2 * π * e := by
      rw [div_le_iff₀ (by norm_num), he]
      have : (twoPiLo60 : ℝ) * (2 ^ 40 - 4 * D) / (4 * 2 ^ 60) ≤ 2 * π * (2 ^ 40 - 4 * D) / 4 := by
        rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
        nlinarith [mul_le_mul_of_nonneg_right hL (by linarith : (0:ℝ) ≤ 2 ^ 40 - 4 * D)]
      have e2 : 2 * π * (1 / 4 - (D : ℝ) / 2 ^ 40) * 2 ^ 40 = 2 * π * (2 ^ 40 - 4 * D) / 4 := by
        field_simp; try ring
      linarith
    set y : ℚ := (Y : ℚ) / 2 ^ 40 with hy
    have hyR : ((y : ℚ) : ℝ) = (Y : ℝ) / 2 ^ 40 := by rw [hy]; push_cast; ring
    have hy0 : (0 : ℚ) ≤ y := by
      have : (0 : ℝ) ≤ ((y : ℚ) : ℝ) := by rw [hyR]; positivity
      exact_mod_cast this
    have hy1 : y ≤ 1 := by
      have : ((y : ℚ) : ℝ) ≤ 1 := by rw [hyR]; nlinarith
      exact_mod_cast this
    have hsin := sinL8_le hy0 hy1
    rw [hyR] at hsin
    have hid : 2 * π * ((D : ℝ) / 2 ^ 40) = π / 2 - 2 * π * e := by rw [he]; ring
    rw [hid, Real.cos_pi_div_two_sub]
    have hmono : Real.sin ((Y : ℝ) / 2 ^ 40) ≤ Real.sin (2 * π * e) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [show (0:ℝ) ≤ (Y : ℝ) / 2 ^ 40 by positivity])
        (by nlinarith) hYle
    have hfl : ((sinL8Num Y / sDenL8 : ℤ) : ℝ) / 2 ^ 40 ≤ ((sinL8 y : ℚ) : ℝ) := by
      apply floor_scaled_le (by norm_num [sDenL8])
      rw [sinL8Num_eq, hy]; unfold sDenL8; push_cast; ring
    linarith
  · -- case 3: 3S ≤ 8D;  cos(2π d) = -cos(2π (1/2 - d))
    have c2' : (2 : ℝ) ^ 40 < 4 * (D : ℝ) := by
      have : ((S : ℤ) : ℝ) < ((4 * D : ℤ) : ℝ) := by exact_mod_cast not_le.mp c2
      push_cast at this; rw [hS] at this; exact this
    have c3' : 3 * (2 : ℝ) ^ 40 ≤ 8 * (D : ℝ) := by
      have : ((S * 3 : ℤ) : ℝ) ≤ ((8 * D : ℤ) : ℝ) := by exact_mod_cast c3
      push_cast at this; rw [hS] at this; linarith
    set Y := (twoPiLo60 * (S - 2 * D)) / (2 * two60) with hY
    have hY1 : (Y : ℝ) ≤ ((twoPiLo60 * (S - 2 * D) : ℤ) : ℝ) / ((2 * two60 : ℤ) : ℝ) :=
      ediv_le_div _ _ (by norm_num [two60])
    have hY2 : ((twoPiLo60 * (S - 2 * D) : ℤ) : ℝ) / ((2 * two60 : ℤ) : ℝ) < (Y : ℝ) + 1 :=
      div_lt_ediv_add_one _ _ (by norm_num [two60])
    push_cast [two60] at hY1 hY2
    rw [hS] at hY1 hY2
    have hY0' : (0 : ℝ) ≤ (Y : ℝ) := by
      have : (0 : ℝ) ≤ (twoPiLo60 : ℝ) * (2 ^ 40 - 2 * D) / (2 * 2 ^ 60) := by
        apply div_nonneg (mul_nonneg (by unfold twoPiLo60; norm_num) (by linarith)) (by norm_num)
      have hint : (-1 : ℤ) < Y := by
        have : (-1 : ℝ) < (Y : ℝ) := by linarith
        exact_mod_cast this
      have : (0 : ℤ) ≤ Y := by omega
      exact_mod_cast this
    set e : ℝ := 1 / 2 - (D : ℝ) / 2 ^ 40 with he
    have he0 : 0 ≤ e := by
      have : (D : ℝ) / 2 ^ 40 ≤ 1 / 2 := by rw [div_le_iff₀ (by norm_num)]; linarith
      rw [he]; linarith
    have he1 : e ≤ 1 / 8 := by
      have : (3 : ℝ) / 8 ≤ (D : ℝ) / 2 ^ 40 := by rw [le_div_iff₀ (by norm_num)]; linarith
      rw [he]; linarith
    have hYle : (Y : ℝ) / 2 ^ 40 ≤ 2 * π * e := by
      rw [div_le_iff₀ (by norm_num), he]
      have : (twoPiLo60 : ℝ) * (2 ^ 40 - 2 * D) / (2 * 2 ^ 60) ≤ 2 * π * (2 ^ 40 - 2 * D) / 2 := by
        rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
        nlinarith [mul_le_mul_of_nonneg_right hL (by linarith : (0:ℝ) ≤ 2 ^ 40 - 2 * D)]
      have e2 : 2 * π * (1 / 2 - (D : ℝ) / 2 ^ 40) * 2 ^ 40 = 2 * π * (2 ^ 40 - 2 * D) / 2 := by
        field_simp; try ring
      linarith
    set y : ℚ := (Y : ℚ) / 2 ^ 40 with hy
    have hyR : ((y : ℚ) : ℝ) = (Y : ℝ) / 2 ^ 40 := by rw [hy]; push_cast; ring
    have hy0 : (0 : ℚ) ≤ y := by
      have : (0 : ℝ) ≤ ((y : ℚ) : ℝ) := by rw [hyR]; positivity
      exact_mod_cast this
    have hy1 : y ≤ 1 := by
      have : ((y : ℚ) : ℝ) ≤ 1 := by rw [hyR]; nlinarith
      exact_mod_cast this
    have hcu := cos_le_cosU7 hy0 hy1
    rw [hyR] at hcu
    have hid : 2 * π * ((D : ℝ) / 2 ^ 40) = π - 2 * π * e := by rw [he]; ring
    rw [hid, Real.cos_pi_sub]
    have hmono : Real.cos (2 * π * e) ≤ Real.cos ((Y : ℝ) / 2 ^ 40) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by nlinarith) hYle
    have hce : ((cosU7 y : ℚ) : ℝ) ≤ ((ceilDiv (cosU7Num Y) cDenU7 : ℤ) : ℝ) / 2 ^ 40 := by
      apply le_ceil_scaled (by norm_num [cDenU7])
      rw [cosU7Num_eq, hy]; unfold cDenU7; push_cast; ring
    push_cast
    linarith
  · -- case 4: S < 4D, 8D < 3S;  cos(2π d) = -sin(2π (d - 1/4))
    have c2' : (2 : ℝ) ^ 40 < 4 * (D : ℝ) := by
      have : ((S : ℤ) : ℝ) < ((4 * D : ℤ) : ℝ) := by exact_mod_cast not_le.mp c2
      push_cast at this; rw [hS] at this; exact this
    have c3' : 8 * (D : ℝ) < 3 * (2 : ℝ) ^ 40 := by
      have : ((8 * D : ℤ) : ℝ) < ((S * 3 : ℤ) : ℝ) := by exact_mod_cast not_le.mp c3
      push_cast at this; rw [hS] at this; linarith
    set Y := ceilDiv (twoPiHi60 * (4 * D - S)) (4 * two60) with hY
    have hY1 : ((twoPiHi60 * (4 * D - S) : ℤ) : ℝ) / ((4 * two60 : ℤ) : ℝ) ≤ (Y : ℝ) :=
      div_le_ceilDiv _ _ (by norm_num [two60])
    have hY2 : (Y : ℝ) < ((twoPiHi60 * (4 * D - S) : ℤ) : ℝ) / ((4 * two60 : ℤ) : ℝ) + 1 :=
      ceilDiv_lt _ _ (by norm_num [two60])
    push_cast [two60] at hY1 hY2
    rw [hS] at hY1 hY2
    set f : ℝ := (D : ℝ) / 2 ^ 40 - 1 / 4 with hf
    have hf0 : 0 ≤ f := by
      have : (1 : ℝ) / 4 ≤ (D : ℝ) / 2 ^ 40 := by rw [le_div_iff₀ (by norm_num)]; linarith
      rw [hf]; linarith
    have hf1 : f ≤ 1 / 8 := by
      have : (D : ℝ) / 2 ^ 40 ≤ 3 / 8 := by rw [div_le_iff₀ (by norm_num)]; linarith
      rw [hf]; linarith
    have hYge : 2 * π * f ≤ (Y : ℝ) / 2 ^ 40 := by
      rw [le_div_iff₀ (by norm_num), hf]
      have : 2 * π * (4 * D - 2 ^ 40) / 4 ≤ (twoPiHi60 : ℝ) * (4 * D - 2 ^ 40) / (4 * 2 ^ 60) := by
        rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
        nlinarith [mul_le_mul_of_nonneg_right hH (by linarith : (0:ℝ) ≤ 4 * D - 2 ^ 40)]
      have e2 : 2 * π * ((D : ℝ) / 2 ^ 40 - 1 / 4) * 2 ^ 40 = 2 * π * (4 * D - 2 ^ 40) / 4 := by
        field_simp; try ring
      linarith
    have hYle : (Y : ℝ) / 2 ^ 40 ≤ 1 := by
      rw [div_le_one (by norm_num)]
      have : (twoPiHi60 : ℝ) * (4 * D - 2 ^ 40) / (4 * 2 ^ 60) ≤ 63 / 10 * (4 * D - 2 ^ 40) / 4 := by
        rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
        nlinarith [mul_le_mul_of_nonneg_right hH2 (by linarith : (0:ℝ) ≤ 4 * D - 2 ^ 40)]
      nlinarith
    have hY0 : (0 : ℝ) ≤ (Y : ℝ) / 2 ^ 40 := le_trans (by positivity) hYge
    set y : ℚ := (Y : ℚ) / 2 ^ 40 with hy
    have hyR : ((y : ℚ) : ℝ) = (Y : ℝ) / 2 ^ 40 := by rw [hy]; push_cast; ring
    have hy0 : (0 : ℚ) ≤ y := by
      have : (0 : ℝ) ≤ ((y : ℚ) : ℝ) := by rw [hyR]; exact hY0
      exact_mod_cast this
    have hy1 : y ≤ 1 := by
      have : ((y : ℚ) : ℝ) ≤ 1 := by rw [hyR]; exact hYle
      exact_mod_cast this
    have hsu := sin_le_sinU7 hy0 hy1
    rw [hyR] at hsu
    have hid : 2 * π * ((D : ℝ) / 2 ^ 40) = 2 * π * f + π / 2 := by rw [hf]; ring
    rw [hid, Real.cos_add_pi_div_two]
    have hmono : Real.sin (2 * π * f) ≤ Real.sin ((Y : ℝ) / 2 ^ 40) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith) (by linarith) hYge
    have hce : ((sinU7 y : ℚ) : ℝ) ≤ ((ceilDiv (sinU7Num Y) sDenU7 : ℤ) : ℝ) / 2 ^ 40 := by
      apply le_ceil_scaled (by norm_num [sDenU7])
      rw [sinU7Num_eq, hy]; unfold sDenU7; push_cast; ring
    push_cast
    linarith

end CirclePacking
