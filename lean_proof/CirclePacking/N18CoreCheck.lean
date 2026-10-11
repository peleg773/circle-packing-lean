import CirclePacking.N18Core
import CirclePacking.N18Exact
import CirclePacking.Q23Bounds

/-!
# The hexagon cores of 18 circles are exact solutions near their rational data

For each variant `m`, the exact lattice coordinates `hexQ m` (in `ℚ(√3)`):
* satisfy every contact of `hexLU m` exactly (`|P_i - P_j|² = 4`), every boundary condition
  (`|P_b|² = ρ₁₉² = 8 + 4√3`) and the gauge (`y₀ = 0`): exact arithmetic in `Q23` (`coreExactOK`);
* lie within `2⁻⁸⁰` of the rational configuration `(hexLU m).ct` (`coreNearOK`, with `√3` between `rl3'` and
  `rh3'`).
-/

namespace CirclePacking

/-- `ρ₁₉² = 8 + 4√3` -/
def rho19sq : Q23 := ⟨8, 0, 4, 0⟩

/-- exact checks of the contacts, boundary conditions and gauge -/
def coreExactOK (d : LUData) (L : List Q23) : Bool :=
  decide (L.length = 2 * d.N) &&
  (List.range d.nC).all (fun r =>
    let dx := L.getD (2 * d.ci r) 0 - L.getD (2 * d.cj r) 0
    let dy := L.getD (2 * d.ci r + 1) 0 - L.getD (2 * d.cj r + 1) 0
    decide (dx * dx + dy * dy = 4)) &&
  (List.range d.nB).all (fun t =>
    let x := L.getD (2 * d.bi t) 0
    let y := L.getD (2 * d.bi t + 1) 0
    decide (x * x + y * y = rho19sq)) &&
  decide (L.getD d.gauge 0 = 0)

/-- rational bounds of `a + c √3` (entries with `b = d = 0`) -/
def lo3 (x : Q23) : ℚ := x.a + min (x.c * rl3') (x.c * rh3')
def hi3 (x : Q23) : ℚ := x.a + max (x.c * rl3') (x.c * rh3')

/-- closeness to the rational data -/
def coreNearOK (d : LUData) (L : List Q23) : Bool :=
  (List.range (2 * d.N)).all (fun c =>
    let x := L.getD c 0
    decide (x.b = 0) && decide (x.d = 0) &&
    decide (d.ctq c - d.rb ≤ lo3 x) && decide (hi3 x ≤ d.ctq c + d.rb))

theorem hex0_exact : coreExactOK hexLU0 hexQ0 = true := by decide +kernel
theorem hex1_exact : coreExactOK hexLU1 hexQ1 = true := by decide +kernel
theorem hex2_exact : coreExactOK hexLU2 hexQ2 = true := by decide +kernel
theorem hex3_exact : coreExactOK hexLU3 hexQ3 = true := by decide +kernel
theorem hex4_exact : coreExactOK hexLU4 hexQ4 = true := by decide +kernel
theorem hex5_exact : coreExactOK hexLU5 hexQ5 = true := by decide +kernel

theorem hex0_near : coreNearOK hexLU0 hexQ0 = true := by decide +kernel
theorem hex1_near : coreNearOK hexLU1 hexQ1 = true := by decide +kernel
theorem hex2_near : coreNearOK hexLU2 hexQ2 = true := by decide +kernel
theorem hex3_near : coreNearOK hexLU3 hexQ3 = true := by decide +kernel
theorem hex4_near : coreNearOK hexLU4 hexQ4 = true := by decide +kernel
theorem hex5_near : coreNearOK hexLU5 hexQ5 = true := by decide +kernel


/-! ### Reading the checks -/

/-- coordinate `c` of a core, as a real number -/
noncomputable def coreC (L : List Q23) (c : ℕ) : ℝ := (L.getD c 0).eval

lemma Q23.eval_eq_of_eq {x y : Q23} (h : x = y) : x.eval = y.eval := by rw [h]

lemma rho19sq_eval : rho19sq.eval = 8 + 4 * √3 := by
  simp [rho19sq, Q23.eval]

lemma coreC_contact {d : LUData} {L : List Q23} (h : coreExactOK d L = true) {r : ℕ} (hr : r < d.nC) :
    (coreC L (2 * d.ci r) - coreC L (2 * d.cj r)) ^ 2 +
      (coreC L (2 * d.ci r + 1) - coreC L (2 * d.cj r + 1)) ^ 2 = 4 := by
  unfold coreExactOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  have e := Q23.eval_eq_of_eq (h.1.1.2 r hr)
  have h4 : (4 : Q23).eval = 4 := by show (Q23.ofQ 4).eval = _; simp
  simp only [Q23.eval_add, Q23.eval_mul, Q23.eval_sub, h4] at e
  simp only [coreC]
  linear_combination e

lemma coreC_bnd {d : LUData} {L : List Q23} (h : coreExactOK d L = true) {t : ℕ} (ht : t < d.nB) :
    coreC L (2 * d.bi t) ^ 2 + coreC L (2 * d.bi t + 1) ^ 2 = 8 + 4 * √3 := by
  unfold coreExactOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  have e := Q23.eval_eq_of_eq (h.1.2 t ht)
  simp only [Q23.eval_add, Q23.eval_mul, rho19sq_eval] at e
  simp only [coreC]
  linear_combination e

lemma coreC_gauge {d : LUData} {L : List Q23} (h : coreExactOK d L = true) : coreC L d.gauge = 0 := by
  unfold coreExactOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  simp only [coreC, h.2, Q23.eval_zero]

lemma sqrt3_bounds' : ((rl3' : ℚ) : ℝ) ≤ √3 ∧ √3 ≤ ((rh3' : ℚ) : ℝ) := by
  have h1 : ((rl3' : ℚ) : ℝ) ^ 2 ≤ 3 := by
    have : rl3' ^ 2 ≤ 3 := by decide +kernel
    exact_mod_cast this
  have h2 : (3 : ℝ) ≤ ((rh3' : ℚ) : ℝ) ^ 2 := by
    have : (3 : ℚ) ≤ rh3' ^ 2 := by decide +kernel
    exact_mod_cast this
  have h0 : (0 : ℝ) ≤ ((rl3' : ℚ) : ℝ) := by
    have : (0 : ℚ) ≤ rl3' := by decide +kernel
    exact_mod_cast this
  have h0' : (0 : ℝ) ≤ ((rh3' : ℚ) : ℝ) := by
    have : (0 : ℚ) ≤ rh3' := by decide +kernel
    exact_mod_cast this
  constructor
  · calc ((rl3' : ℚ) : ℝ) = √(((rl3' : ℚ) : ℝ) ^ 2) := (Real.sqrt_sq h0).symm
      _ ≤ √3 := Real.sqrt_le_sqrt h1
  · calc √3 ≤ √(((rh3' : ℚ) : ℝ) ^ 2) := Real.sqrt_le_sqrt h2
      _ = ((rh3' : ℚ) : ℝ) := Real.sqrt_sq h0'

lemma lo3_le {x : Q23} (hb : x.b = 0) (hd : x.d = 0) : ((lo3 x : ℚ) : ℝ) ≤ x.eval := by
  obtain ⟨h1, h2⟩ := sqrt3_bounds'
  simp only [lo3, Q23.eval, hb, hd, Rat.cast_zero, zero_mul, add_zero]
  push_cast
  have : min ((x.c : ℝ) * ((rl3' : ℚ) : ℝ)) ((x.c : ℝ) * ((rh3' : ℚ) : ℝ)) ≤ (x.c : ℝ) * √3 := by
    rcases le_total 0 (x.c : ℝ) with hc | hc
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left h1 hc)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left h2 hc)
  linarith

lemma le_hi3 {x : Q23} (hb : x.b = 0) (hd : x.d = 0) : x.eval ≤ ((hi3 x : ℚ) : ℝ) := by
  obtain ⟨h1, h2⟩ := sqrt3_bounds'
  simp only [hi3, Q23.eval, hb, hd, Rat.cast_zero, zero_mul, add_zero]
  push_cast
  have : (x.c : ℝ) * √3 ≤ max ((x.c : ℝ) * ((rl3' : ℚ) : ℝ)) ((x.c : ℝ) * ((rh3' : ℚ) : ℝ)) := by
    rcases le_total 0 (x.c : ℝ) with hc | hc
    · exact (mul_le_mul_of_nonneg_left h2 hc).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_left h1 hc).trans (le_max_left _ _)
  linarith

lemma coreC_near {d : LUData} {L : List Q23} (h : coreNearOK d L = true) {c : ℕ} (hc : c < 2 * d.N) :
    |coreC L c - d.ctq c| ≤ d.rb := by
  unfold coreNearOK at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hb, hd⟩, hlo⟩, hhi⟩ := h c hc
  have l1 := lo3_le hb hd
  have l2 := le_hi3 hb hd
  have hlo' : ((d.ctq c - d.rb : ℚ) : ℝ) ≤ ((lo3 (L.getD c 0) : ℚ) : ℝ) := by exact_mod_cast hlo
  have hhi' : ((hi3 (L.getD c 0) : ℚ) : ℝ) ≤ ((d.ctq c + d.rb : ℚ) : ℝ) := by exact_mod_cast hhi
  push_cast at hlo' hhi'
  simp only [coreC]
  rw [abs_le]; constructor <;> linarith

/-- closeness to the rational data, for coordinates in `ℚ(√2, √3)` -/
def coreNearOK23 (d : LUData) (L : List Q23) : Bool :=
  (List.range (2 * d.N)).all (fun c =>
    decide (d.ctq c - d.rb ≤ lo23 (L.getD c 0)) && decide (hi23 (L.getD c 0) ≤ d.ctq c + d.rb))

lemma coreC_near23 {d : LUData} {L : List Q23} (h : coreNearOK23 d L = true) {c : ℕ} (hc : c < 2 * d.N) :
    |coreC L c - d.ctq c| ≤ d.rb := by
  unfold coreNearOK23 at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hlo, hhi⟩ := h c hc
  have l1 := lo23_le (L.getD c 0)
  have l2 := le_hi23 (L.getD c 0)
  have hlo' : ((d.ctq c - d.rb : ℚ) : ℝ) ≤ ((lo23 (L.getD c 0) : ℚ) : ℝ) := by exact_mod_cast hlo
  have hhi' : ((hi23 (L.getD c 0) : ℚ) : ℝ) ≤ ((d.ctq c + d.rb : ℚ) : ℝ) := by exact_mod_cast hhi
  push_cast at hlo' hhi'
  simp only [coreC]
  rw [abs_le]; constructor <;> linarith

end CirclePacking
