import CirclePacking.Algebraic16Data

/-!
# A tower of quadratic extensions over `ℤ[q]` (for the 16-circle elimination)

`ℤ[q] ⊂ K1 = ℤ[q][R] ⊂ K2 = K1[t] ⊂ K3 = K2[wa] ⊂ K4 = K3[wd]` with
`R² = 2(1 - q)`, `t² = 2(1 + q)`, `wa² = 4 - 2(1 + q) U₄(q)²`, `wd² = 1 - 2q + 2t`.
An element of a quadratic extension `A[w]/(w² - δ)` is a pair `(x, y)` standing for `x + y w`.  All
operations are computable; `ev1 … ev4` evaluate an element at real values of `q, R, t, wa, wd` satisfying
the relations, and respect the operations.
-/

namespace CirclePacking.Tw16

/-! ### Quadratic extensions (generic) -/

section QE

variable {A : Type}

def qadd (add : A → A → A) (u v : A × A) : A × A := (add u.1 v.1, add u.2 v.2)
def qneg (neg : A → A) (u : A × A) : A × A := (neg u.1, neg u.2)
/-- `(x + y w)(x' + y' w) = (x x' + y y' δ) + (x y' + y x') w` (the expensive factor comes first) -/
def qmul (add mul : A → A → A) (δ : A) (u v : A × A) : A × A :=
  (add (mul u.1 v.1) (mul (mul u.2 v.2) δ), add (mul u.1 v.2) (mul u.2 v.1))
/-- the norm `x² - y² δ` -/
def qnorm (add mul : A → A → A) (neg : A → A) (δ : A) (u : A × A) : A :=
  add (mul u.1 u.1) (neg (mul (mul u.2 u.2) δ))
/-- evaluation, given the value `w` of the generator -/
def qev (ev : A → ℝ) (w : ℝ) (u : A × A) : ℝ := ev u.1 + ev u.2 * w
/-- componentwise test -/
def qbeq (beq : A → A → Bool) (u v : A × A) : Bool := beq u.1 v.1 && beq u.2 v.2

variable {add mul : A → A → A} {neg : A → A} {ev : A → ℝ}

lemma qev_add (hadd : ∀ a b, ev (add a b) = ev a + ev b) (w : ℝ) (u v : A × A) :
    qev ev w (qadd add u v) = qev ev w u + qev ev w v := by
  simp only [qev, qadd, hadd]; ring

lemma qev_neg (hneg : ∀ a, ev (neg a) = -ev a) (w : ℝ) (u : A × A) :
    qev ev w (qneg neg u) = -qev ev w u := by
  simp only [qev, qneg, hneg]; ring

lemma qev_mul (hadd : ∀ a b, ev (add a b) = ev a + ev b) (hmul : ∀ a b, ev (mul a b) = ev a * ev b)
    (δ : A) (w : ℝ) (hw : w * w = ev δ) (u v : A × A) :
    qev ev w (qmul add mul δ u v) = qev ev w u * qev ev w v := by
  simp only [qev, qmul, hadd, hmul]; rw [← hw]; ring

lemma ev_qnorm (hadd : ∀ a b, ev (add a b) = ev a + ev b) (hmul : ∀ a b, ev (mul a b) = ev a * ev b)
    (hneg : ∀ a, ev (neg a) = -ev a) (δ : A) (w : ℝ) (hw : w * w = ev δ) (u : A × A) :
    ev (qnorm add mul neg δ u) = qev ev w u * (ev u.1 - ev u.2 * w) := by
  simp only [qnorm, hadd, hmul, hneg, qev]; rw [← hw]; ring

lemma qev_eq_of_qbeq {beq : A → A → Bool} (hbeq : ∀ a b, beq a b = true → ev a = ev b) (w : ℝ)
    {u v : A × A} (h : qbeq beq u v = true) : qev ev w u = qev ev w v := by
  simp only [qbeq, Bool.and_eq_true] at h
  simp only [qev, hbeq _ _ h.1, hbeq _ _ h.2]

end QE

/-! ### The tower -/

abbrev K1 := ZPoly × ZPoly
abbrev K2 := K1 × K1
abbrev K3 := K2 × K2
abbrev K4 := K3 × K3

/-- Chebyshev polynomials: `T₃, T₅` (first kind) and `U₂, U₄` (second kind) -/
def zT3 : ZPoly := [0, -3, 0, 4]
def zT5 : ZPoly := [0, 5, 0, -20, 0, 16]
def zU2 : ZPoly := [-1, 0, 4]
def zU4 : ZPoly := [1, 0, -12, 0, 16]

def δR : ZPoly := [2, -2]
def δt : K1 := ([2, 2], [])
def δa : K2 := ((ZPoly.sub [4] (ZPoly.mul (ZPoly.mul zU4 zU4) [2, 2]), []), ([], []))
def δd : K3 := ((([1, -2], []), ([2], [])), (([], []), ([], [])))

def add1 : K1 → K1 → K1 := qadd ZPoly.add
def neg1 : K1 → K1 := qneg ZPoly.neg
def mul1 : K1 → K1 → K1 := qmul ZPoly.add ZPoly.mul δR
def add2 : K2 → K2 → K2 := qadd add1
def neg2 : K2 → K2 := qneg neg1
def mul2 : K2 → K2 → K2 := qmul add1 mul1 δt
def add3 : K3 → K3 → K3 := qadd add2
def neg3 : K3 → K3 := qneg neg2
def mul3 : K3 → K3 → K3 := qmul add2 mul2 δa
def add4 : K4 → K4 → K4 := qadd add3
def neg4 : K4 → K4 := qneg neg3
def mul4 : K4 → K4 → K4 := qmul add3 mul3 δd

def nrm1 : K1 → ZPoly := qnorm ZPoly.add ZPoly.mul ZPoly.neg δR
def nrm2 : K2 → K1 := qnorm add1 mul1 neg1 δt
def nrm3 : K3 → K2 := qnorm add2 mul2 neg2 δa
def nrm4 : K4 → K3 := qnorm add3 mul3 neg3 δd

def beq1 : K1 → K1 → Bool := qbeq ZPoly.beqZ
def beq2 : K2 → K2 → Bool := qbeq beq1
def beq3 : K3 → K3 → Bool := qbeq beq2
def beq4 : K4 → K4 → Bool := qbeq beq3

/-- embedding of `ℤ[q]` -/
def cst (p : ZPoly) : K4 := ((((p, []), ([], [])), (([], []), ([], []))),
  (((([], []), ([], [])), (([], []), ([], [])))))
def gR : K4 := (((([], [1]), ([], [])), (([], []), ([], []))), ((([], []), ([], [])), (([], []), ([], []))))
def gt : K4 := (((([], []), ([1], [])), (([], []), ([], []))), ((([], []), ([], [])), (([], []), ([], []))))
def gwa : K4 := (((([], []), ([], [])), (([1], []), ([], []))), ((([], []), ([], [])), (([], []), ([], []))))
def gwd : K4 := (((([], []), ([], [])), (([], []), ([], []))), ((([1], []), ([], [])), (([], []), ([], []))))

/-! ### Evaluation -/

section ev

variable (q R t wa wd : ℝ)

def ev0 (p : ZPoly) : ℝ := ZPoly.eval p q
def ev1 : K1 → ℝ := qev (ev0 q) R
def ev2 : K2 → ℝ := qev (ev1 q R) t
def ev3 : K3 → ℝ := qev (ev2 q R t) wa
def ev4 : K4 → ℝ := qev (ev3 q R t wa) wd

/-- the relations of the tower -/
structure TowerRel : Prop where
  hR : R * R = 2 - 2 * q
  ht : t * t = 2 + 2 * q
  ha : wa * wa = 4 - (2 + 2 * q) * (16 * q ^ 4 - 12 * q ^ 2 + 1) ^ 2
  hd : wd * wd = 1 - 2 * q + 2 * t

variable {q R t wa wd}

lemma ev0_add (a b : ZPoly) : ev0 q (ZPoly.add a b) = ev0 q a + ev0 q b := ZPoly.eval_add a b q
lemma ev0_mul (a b : ZPoly) : ev0 q (ZPoly.mul a b) = ev0 q a * ev0 q b := ZPoly.eval_mul a b q
lemma ev0_neg (a : ZPoly) : ev0 q (ZPoly.neg a) = -ev0 q a := ZPoly.eval_neg a q
lemma ev0_beq (a b : ZPoly) (h : ZPoly.beqZ a b = true) : ev0 q a = ev0 q b := ZPoly.eval_eq_of_beqZ h q

variable (hT : TowerRel q R t wa wd)
include hT

lemma ev1_add (a b : K1) : ev1 q R (add1 a b) = ev1 q R a + ev1 q R b := qev_add ev0_add R a b
lemma ev1_neg (a : K1) : ev1 q R (neg1 a) = -ev1 q R a := qev_neg ev0_neg R a
lemma ev1_mul (a b : K1) : ev1 q R (mul1 a b) = ev1 q R a * ev1 q R b := by
  refine qev_mul ev0_add ev0_mul δR R ?_ a b
  rw [hT.hR]; simp [ev0, δR, ZPoly.eval]; ring
lemma ev1_beq (a b : K1) (h : beq1 a b = true) : ev1 q R a = ev1 q R b := qev_eq_of_qbeq ev0_beq R h

lemma ev2_add (a b : K2) : ev2 q R t (add2 a b) = ev2 q R t a + ev2 q R t b :=
  qev_add (ev1_add hT) t a b
lemma ev2_neg (a : K2) : ev2 q R t (neg2 a) = -ev2 q R t a := qev_neg (ev1_neg hT) t a
lemma ev2_mul (a b : K2) : ev2 q R t (mul2 a b) = ev2 q R t a * ev2 q R t b := by
  refine qev_mul (ev1_add hT) (ev1_mul hT) δt t ?_ a b
  rw [hT.ht]; simp [ev1, qev, ev0, δt, ZPoly.eval]; ring
lemma ev2_beq (a b : K2) (h : beq2 a b = true) : ev2 q R t a = ev2 q R t b :=
  qev_eq_of_qbeq (ev1_beq hT) t h

lemma ev3_add (a b : K3) : ev3 q R t wa (add3 a b) = ev3 q R t wa a + ev3 q R t wa b :=
  qev_add (ev2_add hT) wa a b
lemma ev3_neg (a : K3) : ev3 q R t wa (neg3 a) = -ev3 q R t wa a := qev_neg (ev2_neg hT) wa a
lemma ev3_mul (a b : K3) : ev3 q R t wa (mul3 a b) = ev3 q R t wa a * ev3 q R t wa b := by
  refine qev_mul (ev2_add hT) (ev2_mul hT) δa wa ?_ a b
  rw [hT.ha]
  simp only [ev2, ev1, qev, ev0, δa, ZPoly.eval_sub, ZPoly.eval_mul, zU4]
  simp [ZPoly.eval]
  ring
lemma ev3_beq (a b : K3) (h : beq3 a b = true) : ev3 q R t wa a = ev3 q R t wa b :=
  qev_eq_of_qbeq (ev2_beq hT) wa h

lemma ev4_add (a b : K4) : ev4 q R t wa wd (add4 a b) = ev4 q R t wa wd a + ev4 q R t wa wd b :=
  qev_add (ev3_add hT) wd a b
lemma ev4_neg (a : K4) : ev4 q R t wa wd (neg4 a) = -ev4 q R t wa wd a := qev_neg (ev3_neg hT) wd a
lemma ev4_mul (a b : K4) : ev4 q R t wa wd (mul4 a b) = ev4 q R t wa wd a * ev4 q R t wa wd b := by
  refine qev_mul (ev3_add hT) (ev3_mul hT) δd wd ?_ a b
  rw [hT.hd]; simp [ev3, ev2, ev1, qev, ev0, δd, ZPoly.eval]; ring
lemma ev4_beq (a b : K4) (h : beq4 a b = true) : ev4 q R t wa wd a = ev4 q R t wa wd b :=
  qev_eq_of_qbeq (ev3_beq hT) wd h

/-! #### Norms of a vanishing element vanish -/

lemma ev1_nrm (u : K1) (h : ev1 q R u = 0) : ev0 q (nrm1 u) = 0 := by
  rw [nrm1, ev_qnorm ev0_add ev0_mul ev0_neg δR R ?_ u]
  · rw [show qev (ev0 q) R u = ev1 q R u from rfl, h, zero_mul]
  · rw [hT.hR]; simp [ev0, δR, ZPoly.eval]; ring
lemma ev2_nrm (u : K2) (h : ev2 q R t u = 0) : ev1 q R (nrm2 u) = 0 := by
  rw [nrm2, ev_qnorm (ev1_add hT) (ev1_mul hT) (ev1_neg hT) δt t ?_ u]
  · rw [show qev (ev1 q R) t u = ev2 q R t u from rfl, h, zero_mul]
  · rw [hT.ht]; simp [ev1, qev, ev0, δt, ZPoly.eval]; ring
lemma ev3_nrm (u : K3) (h : ev3 q R t wa u = 0) : ev2 q R t (nrm3 u) = 0 := by
  rw [nrm3, ev_qnorm (ev2_add hT) (ev2_mul hT) (ev2_neg hT) δa wa ?_ u]
  · rw [show qev (ev2 q R t) wa u = ev3 q R t wa u from rfl, h, zero_mul]
  · rw [hT.ha]
    simp only [ev2, ev1, qev, ev0, δa, ZPoly.eval_sub, ZPoly.eval_mul, zU4]
    simp [ZPoly.eval]
    ring
lemma ev4_nrm (u : K4) (h : ev4 q R t wa wd u = 0) : ev3 q R t wa (nrm4 u) = 0 := by
  rw [nrm4, ev_qnorm (ev3_add hT) (ev3_mul hT) (ev3_neg hT) δd wd ?_ u]
  · rw [show qev (ev3 q R t wa) wd u = ev4 q R t wa wd u from rfl, h, zero_mul]
  · rw [hT.hd]; simp [ev3, ev2, ev1, qev, ev0, δd, ZPoly.eval]; ring

end ev

/-! #### Values of the generators -/

section gens

variable (q R t wa wd : ℝ)

lemma ev4_cst (p : ZPoly) : ev4 q R t wa wd (cst p) = ZPoly.eval p q := by
  simp [cst, ev4, ev3, ev2, ev1, qev, ev0]
lemma ev4_gR : ev4 q R t wa wd gR = R := by simp [gR, ev4, ev3, ev2, ev1, qev, ev0, ZPoly.eval]
lemma ev4_gt : ev4 q R t wa wd gt = t := by simp [gt, ev4, ev3, ev2, ev1, qev, ev0, ZPoly.eval]
lemma ev4_gwa : ev4 q R t wa wd gwa = wa := by simp [gwa, ev4, ev3, ev2, ev1, qev, ev0, ZPoly.eval]
lemma ev4_gwd : ev4 q R t wa wd gwd = wd := by simp [gwd, ev4, ev3, ev2, ev1, qev, ev0, ZPoly.eval]

end gens

end CirclePacking.Tw16
