import Mathlib

/-!
# Integer polynomials as coefficient lists, with a verified evaluation

A `ZPoly` is a list of integers, the coefficients from the constant term up.  The operations below are
computable (so that identities between explicit polynomials can be decided by evaluation in the kernel),
and `eval` turns them into the corresponding operations on values in any commutative ring.
-/

namespace CirclePacking

/-- an integer polynomial: its coefficients, from the constant term up -/
abbrev ZPoly := List ℤ

namespace ZPoly

def add : ZPoly → ZPoly → ZPoly
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: add p q

def neg (p : ZPoly) : ZPoly := p.map (fun a => -a)

def sub (p q : ZPoly) : ZPoly := add p (neg q)

def smul (c : ℤ) (p : ZPoly) : ZPoly := p.map (fun a => c * a)

def mul : ZPoly → ZPoly → ZPoly
  | [], _ => []
  | a :: p, q => add (smul a q) (0 :: mul p q)

def pow (p : ZPoly) : ℕ → ZPoly
  | 0 => [1]
  | n + 1 => mul (pow p n) p

/-- drop the trailing zero coefficients -/
def trim : ZPoly → ZPoly
  | [] => []
  | a :: p => match trim p with
    | [] => if a = 0 then [] else [a]
    | b :: q => a :: b :: q

/-- the formal derivative -/
def derivAux : ℕ → ZPoly → ZPoly
  | _, [] => []
  | k, a :: p => (k * a) :: derivAux (k + 1) p

def deriv : ZPoly → ZPoly
  | [] => []
  | _ :: p => derivAux 1 p

section eval

variable {R : Type*} [CommRing R]

/-- evaluation at `x` (Horner) -/
def eval : ZPoly → R → R
  | [], _ => 0
  | a :: p, x => (a : R) + x * eval p x

@[simp] lemma eval_nil (x : R) : eval [] x = 0 := rfl
@[simp] lemma eval_cons (a : ℤ) (p : ZPoly) (x : R) : eval (a :: p) x = (a : R) + x * eval p x := rfl

lemma eval_add (p q : ZPoly) (x : R) : eval (add p q) x = eval p x + eval q x := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih =>
    cases q with
    | nil => simp [add]
    | cons b q => simp [add, ih]; ring

lemma eval_neg (p : ZPoly) (x : R) : eval (neg p) x = -eval p x := by
  induction p with
  | nil => simp [neg]
  | cons a p ih =>
    simp only [neg, List.map_cons, eval_cons] at ih ⊢
    rw [ih]; push_cast; ring

lemma eval_sub (p q : ZPoly) (x : R) : eval (sub p q) x = eval p x - eval q x := by
  rw [sub, eval_add, eval_neg]; ring

lemma eval_smul (c : ℤ) (p : ZPoly) (x : R) : eval (smul c p) x = (c : R) * eval p x := by
  induction p with
  | nil => simp [smul]
  | cons a p ih =>
    simp only [smul, List.map_cons, eval_cons] at ih ⊢
    rw [ih]; push_cast; ring

lemma eval_mul (p q : ZPoly) (x : R) : eval (mul p q) x = eval p x * eval q x := by
  induction p with
  | nil => simp [mul]
  | cons a p ih =>
    simp only [mul, eval_add, eval_smul, eval_cons, ih]
    push_cast; ring

lemma eval_pow (p : ZPoly) (n : ℕ) (x : R) : eval (pow p n) x = eval p x ^ n := by
  induction n with
  | zero => simp [pow]
  | succ n ih => simp [pow, eval_mul, ih, pow_succ]

lemma eval_trim (p : ZPoly) (x : R) : eval (trim p) x = eval p x := by
  induction p with
  | nil => simp [trim]
  | cons a p ih =>
    simp only [trim]
    rcases h : trim p with _ | ⟨b, q⟩
    · rw [h] at ih
      simp only [eval_nil] at ih
      split_ifs with ha
      · simp [ha, ← ih]
      · simp [← ih]
    · rw [h] at ih
      simp only [eval_cons] at ih ⊢
      rw [← ih]

/-- a decidable test for equality of the polynomial functions -/
def beqZ (p q : ZPoly) : Bool := trim (sub p q) == []

lemma eval_eq_of_beqZ {p q : ZPoly} (h : beqZ p q = true) (x : R) : eval p x = eval q x := by
  have h' : trim (sub p q) = [] := by simpa [beqZ] using h
  have := eval_trim (sub p q) x
  rw [h', eval_sub, eval_nil] at this
  exact (sub_eq_zero.mp this.symm)

end eval

/-! ### Derivative and a mean-value bound (real arguments) -/

/-- `∑ |a_i|`: bounds `|p x|` for `|x| ≤ 1` -/
def absSum (p : ZPoly) : ℕ := (p.map Int.natAbs).sum

lemma abs_eval_le_absSum (p : ZPoly) {x : ℝ} (hx : |x| ≤ 1) : |eval p x| ≤ (absSum p : ℝ) := by
  induction p with
  | nil => simp [absSum]
  | cons a p ih =>
    have hs : (absSum (a :: p) : ℝ) = (a.natAbs : ℝ) + (absSum p : ℝ) := by
      simp [absSum]
    rw [hs, eval_cons]
    have h1 : |(a : ℝ) + x * eval p x| ≤ |(a : ℝ)| + |x| * |eval p x| := by
      rw [← abs_mul]; exact abs_add_le _ _
    have h2 : |x| * |eval p x| ≤ (absSum p : ℝ) := by
      calc |x| * |eval p x| ≤ 1 * |eval p x| := by gcongr
        _ ≤ _ := by rw [one_mul]; exact ih
    have h3 : |(a : ℝ)| = (a.natAbs : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
    linarith

/-! ### Ring homomorphisms -/

lemma eval_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (p : ZPoly) (x : R) :
    f (eval p x) = eval p (f x) := by
  induction p with
  | nil => simp
  | cons a p ih => simp [ih]

/-! ### Derivative (real arguments) -/

/-- the derivative, in a form adapted to Horner evaluation: `(a + x p)' = p + x p'` -/
def dP : ZPoly → ZPoly
  | [] => []
  | _ :: p => add p (0 :: dP p)

lemma hasDerivAt_eval (p : ZPoly) (x : ℝ) : HasDerivAt (fun y : ℝ => eval p y) (eval (dP p) x) x := by
  induction p with
  | nil => simpa [dP] using hasDerivAt_const x (0 : ℝ)
  | cons a p ih =>
    have h1 : HasDerivAt (fun y : ℝ => y * eval p y) (1 * eval p x + x * eval (dP p) x) x :=
      (hasDerivAt_id' x).mul ih
    have h2 := h1.const_add (a : ℝ)
    have e : (fun y : ℝ => eval (a :: p) y) = fun y => (a : ℝ) + y * eval p y := rfl
    rw [e]
    simp only [dP, eval_add, eval_cons, Int.cast_zero, zero_add]
    convert h2 using 1
    ring

/-! ### Taylor shift at a rational point (scaled to integers) -/

/-- `shiftS p n m`: the integer polynomial `z ↦ m^(len p - 1) p((n + z)/m)` -/
def shiftS (n m : ℤ) : ZPoly → ZPoly
  | [] => []
  | a :: p => add [a * m ^ p.length] (mul (shiftS n m p) [n, 1])

lemma eval_shiftS (n m : ℤ) (hm : (m : ℝ) ≠ 0) (p : ZPoly) (z : ℝ) :
    eval (shiftS n m p) z = (m : ℝ) ^ (p.length - 1) * eval p ((n + z) / m) := by
  induction p with
  | nil => simp [shiftS]
  | cons a p ih =>
    simp only [shiftS, eval_add, eval_mul, eval_cons, eval_nil, ih, List.length_cons]
    rcases p with _ | ⟨b, p⟩
    · simp
    · simp only [List.length_cons, Nat.add_sub_cancel, eval_cons]
      push_cast
      field_simp
      ring

/-- all coefficients nonnegative and the constant term positive -/
def posCoeffs : ZPoly → Bool
  | [] => false
  | a :: p => decide (0 < a) && p.all (fun b => decide (0 ≤ b))

lemma eval_nonneg_of_all (p : ZPoly) (hp : p.all (fun b => decide (0 ≤ b)) = true) {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ eval p z := by
  induction p with
  | nil => simp
  | cons a p ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hp
    simp only [eval_cons]
    have : (0 : ℝ) ≤ a := by exact_mod_cast hp.1
    have := ih hp.2
    positivity

lemma eval_pos_of_posCoeffs {p : ZPoly} (hp : posCoeffs p = true) {z : ℝ} (hz : 0 ≤ z) : 0 < eval p z := by
  rcases p with _ | ⟨a, p⟩
  · simp [posCoeffs] at hp
  · simp only [posCoeffs, Bool.and_eq_true, decide_eq_true_eq] at hp
    simp only [eval_cons]
    have h1 : (0 : ℝ) < a := by exact_mod_cast hp.1
    have h2 := eval_nonneg_of_all p hp.2 hz
    positivity

/-! ### As a Mathlib polynomial -/

/-- the Mathlib polynomial with these coefficients -/
noncomputable def toPoly : ZPoly → Polynomial ℤ
  | [] => 0
  | a :: p => Polynomial.C a + Polynomial.X * toPoly p

lemma aeval_toPoly {R : Type*} [CommRing R] (p : ZPoly) (x : R) : Polynomial.aeval x (toPoly p) = eval p x := by
  induction p with
  | nil => simp [toPoly]
  | cons a p ih => simp [toPoly, ih]

end ZPoly

end CirclePacking
