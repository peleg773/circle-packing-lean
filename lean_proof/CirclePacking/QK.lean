import Mathlib

/-!
# The number field `K = ℚ(s)`, `s = sin (π/5)`

Elements are `a + b s + c s² + d s³` with rational coefficients; `s` satisfies `16 s⁴ - 20 s² + 5 = 0`.
Exact arithmetic is computable; `QK.eval` is a ring homomorphism into `ℝ`.
-/

open Real

namespace CirclePacking

/-- elements of `K = ℚ(s)`, `s = sin(π/5)`: `a + b s + c s² + d s³` -/
structure QK where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ
deriving DecidableEq, Inhabited, Repr

namespace QK

def ofQ (q : ℚ) : QK := ⟨q, 0, 0, 0⟩
def add (x y : QK) : QK := ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩
def neg (x : QK) : QK := ⟨-x.a, -x.b, -x.c, -x.d⟩
def sub (x y : QK) : QK := ⟨x.a - y.a, x.b - y.b, x.c - y.c, x.d - y.d⟩
def mul (x y : QK) : QK :=
  let p0 := x.a * y.a
  let p1 := x.a * y.b + x.b * y.a
  let p2 := x.a * y.c + x.b * y.b + x.c * y.a
  let p3 := x.a * y.d + x.b * y.c + x.c * y.b + x.d * y.a
  let p4 := x.b * y.d + x.c * y.c + x.d * y.b
  let p5 := x.c * y.d + x.d * y.c
  let p6 := x.d * y.d
  let q4 := p4 + p6 * (20 / 16)
  ⟨p0 + q4 * (-5 / 16), p1 + p5 * (-5 / 16), p2 + p6 * (-5 / 16) + q4 * (20 / 16), p3 + p5 * (20 / 16)⟩

instance : Add QK := ⟨add⟩
instance : Neg QK := ⟨neg⟩
instance : Sub QK := ⟨sub⟩
instance : Mul QK := ⟨mul⟩
instance : OfNat QK n := ⟨ofQ n⟩

/-- `s = sin (π/5)` -/
noncomputable def s5 : ℝ := Real.sin (π / 5)

lemma s5_sq : s5 ^ 2 = (10 - 2 * √5) / 16 := by
  have hc := Real.cos_pi_div_five
  have h := Real.sin_sq_add_cos_sq (π / 5)
  unfold s5
  rw [hc] at h
  have h5 : (√5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h5]

lemma s5_poly : 16 * s5 ^ 4 - 20 * s5 ^ 2 + 5 = 0 := by
  have h := s5_sq
  have h5 : (√5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have : s5 ^ 4 = (s5 ^ 2) ^ 2 := by ring
  rw [this, h]
  nlinarith [h5]

/-- evaluation in `ℝ` -/
noncomputable def eval (x : QK) : ℝ := x.a + x.b * s5 + x.c * s5 ^ 2 + x.d * s5 ^ 3

@[simp] lemma eval_add (x y : QK) : (x + y).eval = x.eval + y.eval := by
  show (add x y).eval = _
  simp only [add, eval]; push_cast; ring

@[simp] lemma eval_sub (x y : QK) : (x - y).eval = x.eval - y.eval := by
  show (sub x y).eval = _
  simp only [sub, eval]; push_cast; ring

@[simp] lemma eval_neg (x : QK) : (-x).eval = -x.eval := by
  show (neg x).eval = _
  simp only [neg, eval]; push_cast; ring

@[simp] lemma eval_mul (x y : QK) : (x * y).eval = x.eval * y.eval := by
  show (mul x y).eval = _
  simp only [mul, eval]
  push_cast
  have hs := s5_poly
  linear_combination
    (-((x.d : ℝ) * y.d * s5 ^ 2 + ((x.c : ℝ) * y.d + x.d * y.c) * s5 +
      ((x.b : ℝ) * y.d + x.c * y.c + x.d * y.b + x.d * y.d * (20 / 16))) / 16) * hs

@[simp] lemma eval_ofQ (q : ℚ) : (ofQ q).eval = q := by simp [ofQ, eval]

@[simp] lemma eval_ofNat (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : QK).eval = n := by
  show (ofQ n).eval = _; simp

@[simp] lemma eval_zero : (0 : QK).eval = 0 := by show (ofQ 0).eval = 0; simp
@[simp] lemma eval_one : (1 : QK).eval = 1 := by show (ofQ 1).eval = 1; simp

/-! ### Rational bounds -/

/-- rational bounds `sLo ≤ s5 ≤ sHi` -/
def sLo : ℚ := 5877852522924731 / 10000000000000000
def sHi : ℚ := 5877852522924732 / 10000000000000000

lemma sqrt5_bounds : (22360679774997896 / 10000000000000000 : ℝ) < √5 ∧
    √5 < (22360679774997897 / 10000000000000000 : ℝ) := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

lemma s5_pos : 0 < s5 := by
  unfold s5; apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [Real.pi_pos]

lemma s5_bounds : (sLo : ℝ) ≤ s5 ∧ s5 ≤ (sHi : ℝ) := by
  have h2 := s5_sq
  have ⟨hl, hh⟩ := sqrt5_bounds
  have hp := s5_pos
  constructor
  · unfold sLo; push_cast
    nlinarith
  · unfold sHi; push_cast
    nlinarith

/-- interval enclosure of `eval x` from the bounds on `s` -/
def lo (x : QK) : ℚ :=
  x.a + min (x.b * sLo) (x.b * sHi) + min (x.c * sLo ^ 2) (x.c * sHi ^ 2) + min (x.d * sLo ^ 3) (x.d * sHi ^ 3)
def hi (x : QK) : ℚ :=
  x.a + max (x.b * sLo) (x.b * sHi) + max (x.c * sLo ^ 2) (x.c * sHi ^ 2) + max (x.d * sLo ^ 3) (x.d * sHi ^ 3)

lemma term_bounds {t lo' hi' : ℝ} (_h0 : 0 ≤ lo') (hl : lo' ≤ t) (hh : t ≤ hi') (q : ℚ) :
    min ((q : ℝ) * lo') (q * hi') ≤ q * t ∧ (q : ℝ) * t ≤ max ((q : ℝ) * lo') (q * hi') := by
  rcases le_total 0 (q : ℝ) with hq | hq
  · constructor
    · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left hl hq)
    · exact le_trans (mul_le_mul_of_nonneg_left hh hq) (le_max_right _ _)
  · constructor
    · exact le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left hh hq)
    · exact le_trans (mul_le_mul_of_nonpos_left hl hq) (le_max_left _ _)

lemma lo_le_eval (x : QK) : ((lo x : ℚ) : ℝ) ≤ x.eval := by
  obtain ⟨hl, hh⟩ := s5_bounds
  have h0 : (0 : ℝ) ≤ sLo := by unfold sLo; norm_num
  have t1 := (term_bounds h0 hl hh x.b).1
  have t2 := (term_bounds (by positivity) (pow_le_pow_left₀ h0 hl 2) (pow_le_pow_left₀ (le_trans h0 hl) hh 2) x.c).1
  have t3 := (term_bounds (by positivity) (pow_le_pow_left₀ h0 hl 3) (pow_le_pow_left₀ (le_trans h0 hl) hh 3) x.d).1
  unfold lo eval; push_cast
  linarith

lemma eval_le_hi (x : QK) : x.eval ≤ ((hi x : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := s5_bounds
  have h0 : (0 : ℝ) ≤ sLo := by unfold sLo; norm_num
  have t1 := (term_bounds h0 hl hh x.b).2
  have t2 := (term_bounds (by positivity) (pow_le_pow_left₀ h0 hl 2) (pow_le_pow_left₀ (le_trans h0 hl) hh 2) x.c).2
  have t3 := (term_bounds (by positivity) (pow_le_pow_left₀ h0 hl 3) (pow_le_pow_left₀ (le_trans h0 hl) hh 3) x.d).2
  unfold hi eval; push_cast
  linarith

end QK

end CirclePacking
