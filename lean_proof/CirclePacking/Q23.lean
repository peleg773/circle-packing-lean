import Mathlib

/-!
# Exact arithmetic in `ℚ(√2, √3)`

Elements `a + b √2 + c √3 + d √6` with rational coefficients, exact `+ - *`, evaluation in `ℝ`, and rational
bounds.  The 19-circle lattice (centre, hexagon of radius `2`, twelve circles at `ρ₁₉ = √6 + √2` at the angles
`15° + 30° j`), and with it every rigid core used for 18 circles, has coordinates in this field.
-/

namespace CirclePacking

/-- `a + b √2 + c √3 + d √6` -/
structure Q23 where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ
deriving DecidableEq, Inhabited, Repr

namespace Q23

def ofQ (q : ℚ) : Q23 := ⟨q, 0, 0, 0⟩
def add (x y : Q23) : Q23 := ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩
def neg (x : Q23) : Q23 := ⟨-x.a, -x.b, -x.c, -x.d⟩
def sub (x y : Q23) : Q23 := ⟨x.a - y.a, x.b - y.b, x.c - y.c, x.d - y.d⟩
/-- `√2² = 2`, `√3² = 3`, `√2 √3 = √6`, `√2 √6 = 2 √3`, `√3 √6 = 3 √2`, `√6² = 6` -/
def mul (x y : Q23) : Q23 :=
  ⟨x.a * y.a + 2 * x.b * y.b + 3 * x.c * y.c + 6 * x.d * y.d,
   x.a * y.b + x.b * y.a + 3 * (x.c * y.d + x.d * y.c),
   x.a * y.c + x.c * y.a + 2 * (x.b * y.d + x.d * y.b),
   x.a * y.d + x.d * y.a + x.b * y.c + x.c * y.b⟩

instance : Add Q23 := ⟨add⟩
instance : Neg Q23 := ⟨neg⟩
instance : Sub Q23 := ⟨sub⟩
instance : Mul Q23 := ⟨mul⟩
instance : OfNat Q23 n := ⟨ofQ n⟩

/-- evaluation in `ℝ` -/
noncomputable def eval (x : Q23) : ℝ := x.a + x.b * √2 + x.c * √3 + x.d * (√2 * √3)

lemma sq2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
lemma sq3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

@[simp] lemma eval_add (x y : Q23) : (x + y).eval = x.eval + y.eval := by
  show (add x y).eval = _
  simp only [add, eval]; push_cast; ring

@[simp] lemma eval_sub (x y : Q23) : (x - y).eval = x.eval - y.eval := by
  show (sub x y).eval = _
  simp only [sub, eval]; push_cast; ring

@[simp] lemma eval_neg (x : Q23) : (-x).eval = -x.eval := by
  show (neg x).eval = _
  simp only [neg, eval]; push_cast; ring

@[simp] lemma eval_mul (x y : Q23) : (x * y).eval = x.eval * y.eval := by
  show (mul x y).eval = _
  simp only [mul, eval]
  push_cast
  have h2 := sq2
  have h3 := sq3
  linear_combination
    (-((x.b : ℝ) * y.b) - (x.d : ℝ) * y.d * √3 ^ 2 - ((x.b : ℝ) * y.d + (x.d : ℝ) * y.b) * √3) * h2 +
    (-((x.c : ℝ) * y.c) - 2 * (x.d : ℝ) * y.d - ((x.c : ℝ) * y.d + (x.d : ℝ) * y.c) * √2) * h3

@[simp] lemma eval_ofQ (q : ℚ) : (ofQ q).eval = q := by simp [ofQ, eval]

@[simp] lemma eval_ofNat (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : Q23).eval = n := by
  show (ofQ n).eval = _; simp

@[simp] lemma eval_zero : (0 : Q23).eval = 0 := by show (ofQ 0).eval = 0; simp
@[simp] lemma eval_one : (1 : Q23).eval = 1 := by show (ofQ 1).eval = 1; simp

end Q23

end CirclePacking
