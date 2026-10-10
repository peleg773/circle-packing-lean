import CirclePacking.Tower16

/-!
# The elimination identity, for real numbers

`H16_eval_eq_zero`: if real numbers `q, R, t, wa, wd` satisfy the tower relations and the scaled last contact
equation `F16real = 0`, then `q` is a root of `H16` (from the kernel-checked identities in `Tower16.lean`).
-/

namespace CirclePacking.Tw16

local infixl:65 " +' " => add4
local infixl:70 " *' " => mul4
local prefix:max "-'" => neg4

/-! ### Consequence for real numbers -/

/-- the real counterpart of `f16` (`Lq = 1 - q`; `â, d̂, D̂, N̂` as in the docstrings of `Tower16Data`) -/
noncomputable def F16real (q R t wa wd : ℝ) : ℝ :=
  let Lq := 1 - q
  let A := -(R * ZPoly.eval zT5 q) - Lq * wa
  let D := -(R * q) + Lq * wd
  let DD := (A + R * ZPoly.eval zT3 q) - (A - D) * t * ZPoly.eval zU2 q
  let Nb := (A * A - R * R) + t * ZPoly.eval zU2 q * (D * D + Lq * Lq - A * A)
  let X1 := 2 * DD * A - Nb
  let X2 := (A - D) * Nb + DD * (D * D + Lq * Lq - A * A)
  Lq * Lq * (X1 * X1) + X2 * X2 - 16 * Lq * Lq * Lq * Lq * DD * DD

section real

variable {q R t wa wd : ℝ} (hT : TowerRel q R t wa wd)
include hT

lemma ev4_vF : ev4 q R t wa wd vF = F16real q R t wa wd := by
  have eq1 : ZPoly.eval ([1, -1] : ZPoly) q = 1 - q := by simp [ZPoly.eval]; ring
  have eqq : ZPoly.eval ([0, 1] : ZPoly) q = q := by simp [ZPoly.eval]
  have e2 : ZPoly.eval ([2] : ZPoly) q = 2 := by simp [ZPoly.eval]
  have e16 : ZPoly.eval ([16] : ZPoly) q = 16 := by simp [ZPoly.eval]
  have hA : ev4 q R t wa wd vA = -(R * ZPoly.eval zT5 q) - (1 - q) * wa := by
    rw [← ev4_beq hT _ _ vA_ok]
    simp only [ev4_add hT, ev4_neg hT, ev4_mul hT, ev4_gR, ev4_cst, ev4_gwa, kL, eq1]; ring
  have hD : ev4 q R t wa wd vD = -(R * q) + (1 - q) * wd := by
    rw [← ev4_beq hT _ _ vD_ok]
    simp only [ev4_add hT, ev4_neg hT, ev4_mul hT, ev4_gR, ev4_cst, ev4_gwd, kL, kq, eq1, eqq]
  have hDD : ev4 q R t wa wd vDD = (ev4 q R t wa wd vA + R * ZPoly.eval zT3 q) -
      (ev4 q R t wa wd vA - ev4 q R t wa wd vD) * t * ZPoly.eval zU2 q := by
    rw [← ev4_beq hT _ _ vDD_ok]
    simp only [ev4_add hT, ev4_neg hT, ev4_mul hT, ev4_gR, ev4_cst, ev4_gt]; ring
  have hNb : ev4 q R t wa wd vNb = (ev4 q R t wa wd vA * ev4 q R t wa wd vA - R * R) +
      t * ZPoly.eval zU2 q * (ev4 q R t wa wd vD * ev4 q R t wa wd vD + (1 - q) * (1 - q) -
        ev4 q R t wa wd vA * ev4 q R t wa wd vA) := by
    rw [← ev4_beq hT _ _ vNb_ok]
    simp only [ev4_add hT, ev4_neg hT, ev4_mul hT, ev4_gR, ev4_cst, ev4_gt, kL, eq1]; ring
  have hX1 : ev4 q R t wa wd vX1 = 2 * ev4 q R t wa wd vDD * ev4 q R t wa wd vA - ev4 q R t wa wd vNb := by
    rw [← ev4_beq hT _ _ vX1_ok]
    simp only [ev4_add hT, ev4_neg hT, ev4_mul hT, ev4_cst, e2]; ring
  have hX2 : ev4 q R t wa wd vX2 = (ev4 q R t wa wd vA - ev4 q R t wa wd vD) * ev4 q R t wa wd vNb +
      ev4 q R t wa wd vDD * (ev4 q R t wa wd vD * ev4 q R t wa wd vD + (1 - q) * (1 - q) -
        ev4 q R t wa wd vA * ev4 q R t wa wd vA) := by
    rw [← ev4_beq hT _ _ vX2_ok]
    simp only [ev4_add hT, ev4_neg hT, ev4_mul hT, ev4_cst, kL, eq1]; ring
  have hF : ev4 q R t wa wd vF = (1 - q) * (1 - q) * (ev4 q R t wa wd vX1 * ev4 q R t wa wd vX1) +
      ev4 q R t wa wd vX2 * ev4 q R t wa wd vX2 -
      16 * (1 - q) * (1 - q) * (1 - q) * (1 - q) * ev4 q R t wa wd vDD * ev4 q R t wa wd vDD := by
    rw [← ev4_beq hT _ _ vF_ok]
    simp only [ev4_add hT, ev4_neg hT, ev4_mul hT, ev4_cst, kL, eq1, e16]; ring
  rw [hF, hX1, hX2, hNb, hDD, hA, hD]
  simp only [F16real]

/-- **A solution of the reduced system has `H16(q) = 0`.** -/
theorem H16_eval_eq_zero (hF : F16real q R t wa wd = 0) (hq1 : q ≠ 1) (hq2 : 1 + 2 * q ≠ 0) :
    ZPoly.eval H16coeffs q = 0 := by
  have h4 : ev4 q R t wa wd vF = 0 := by rw [ev4_vF hT, hF]
  have h3 : ev3 q R t wa vN4 = 0 := by rw [← ev3_beq hT _ _ vN4_ok]; exact ev4_nrm hT _ h4
  have h2 : ev2 q R t vN3 = 0 := by rw [← ev2_beq hT _ _ vN3_ok]; exact ev3_nrm hT _ h3
  have h1 : ev1 q R vN2 = 0 := by rw [← ev1_beq hT _ _ vN2_ok]; exact ev2_nrm hT _ h2
  have h0 : ZPoly.eval vN1 q = 0 := by
    have := ev1_nrm hT _ h1
    rwa [show ev0 q (nrm1 vN2) = ZPoly.eval (nrm1 vN2) q from rfl, ZPoly.eval_eq_of_beqZ vN1_ok q] at this
  rw [ZPoly.eval_eq_of_beqZ vN1_eq q, ZPoly.eval_smul, ZPoly.eval_mul,
    ← ZPoly.eval_eq_of_beqZ vH2_ok q, ← ZPoly.eval_eq_of_beqZ vP_ok q, ZPoly.eval_mul, ZPoly.eval_mul,
    ZPoly.eval_pow, ZPoly.eval_pow] at h0
  have hb : ZPoly.eval ([1, 2] : ZPoly) q = 1 + 2 * q := by simp [ZPoly.eval]; ring
  have hc : ZPoly.eval ([-1, 1] : ZPoly) q = q - 1 := by simp [ZPoly.eval]; ring
  rw [hb, hc] at h0
  have hq1' : q - 1 ≠ 0 := sub_ne_zero.mpr hq1
  have hpow : (1 + 2 * q) ^ 24 * (q - 1) ^ 96 ≠ 0 := mul_ne_zero (pow_ne_zero _ hq2) (pow_ne_zero _ hq1')
  have h2pow : ((2 ^ 100 : ℤ) : ℝ) ≠ 0 := by norm_num
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd h h2pow
  · rcases mul_eq_zero.mp h with h | h
    · exact mul_self_eq_zero.mp h
    · exact absurd h hpow

end real

end CirclePacking.Tw16
