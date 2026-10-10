import CirclePacking.N16Data
import CirclePacking.Angle
import C16Compute

/-!
# The record configuration of 16 circles

`c*` is the exact solution of the contact system near the rational configuration `n16ut` (existence by
`exists_solution`).  We prove its polar brackets (`r16Lo … a16Hi`), its container radius bounds, and that it
is a packing.
-/

open Real Finset

namespace CirclePacking

set_option maxRecDepth 100000 in
/-- the rational certificate checks -/
theorem n16K_ok : n16K.ok = true := by decide +kernel

lemma n16K_n : n16K.n = 33 := rfl

/-- the exact record configuration: coordinates `2p`, `2p+1`, then `P = ρ*²` -/
noncomputable def u16 : ℕ → ℝ := Classical.choose (exists_solution n16K n16K_ok)

lemma u16_close : ∀ k < 33, |u16 k - n16K.utq k| ≤ n16K.rb :=
  (Classical.choose_spec (exists_solution n16K n16K_ok)).1

lemma u16_eq : ∀ r < 33, n16K.F u16 r = 0 :=
  (Classical.choose_spec (exists_solution n16K n16K_ok)).2

/-- point `p` of the record configuration -/
noncomputable def C16 (p : ℕ) : ℂ := ⟨u16 (2 * p), u16 (2 * p + 1)⟩

/-- the squared container parameter and the container parameter of the record configuration -/
noncomputable def P16s : ℝ := u16 32
noncomputable def ρ16 : ℝ := √P16s

/-! ### Exact equations -/

lemma n16_nC : n16K.nC = 21 := rfl
lemma n16_nB : n16K.nB = 11 := rfl

lemma C16_contact {r : ℕ} (hr : r < 21) :
    (u16 (2 * n16K.ci r) - u16 (2 * n16K.cj r)) ^ 2 + (u16 (2 * n16K.ci r + 1) - u16 (2 * n16K.cj r + 1)) ^ 2 = 4 := by
  have h := u16_eq r (by omega)
  simp only [KData.F, show r < n16K.nC from by rw [n16_nC]; exact hr, ite_true] at h
  linarith

lemma C16_bnd {t : ℕ} (ht : t < 11) :
    u16 (2 * n16K.bi t) ^ 2 + u16 (2 * n16K.bi t + 1) ^ 2 = P16s := by
  have h := u16_eq (21 + t) (by omega)
  have h1 : ¬ (21 + t < n16K.nC) := by rw [n16_nC]; omega
  have h2 : 21 + t < n16K.nC + n16K.nB := by rw [n16_nC, n16_nB]; omega
  simp only [KData.F, h1, h2, ite_false, ite_true, show 21 + t - n16K.nC = t by rw [n16_nC]; omega] at h
  unfold P16s
  rw [show 2 * n16K.N = 32 from rfl] at h
  linarith

lemma C16_gauge : u16 1 = 0 := by
  have h := u16_eq 32 (by omega)
  have h1 : ¬ (32 < n16K.nC) := by rw [n16_nC]; omega
  have h2 : ¬ (32 < n16K.nC + n16K.nB) := by rw [n16_nC, n16_nB]; omega
  simp only [KData.F, h1, h2, ite_false] at h
  exact h

/-! ### Certified brackets -/

/-- lower bound of `c * Y` for `c ∈ [cl, ch]`, `Y ∈ [yl, yh]` -/
def mulLB (cl ch yl yh : ℚ) : ℚ := min (min (cl * yl) (cl * yh)) (min (ch * yl) (ch * yh))
/-- upper bound of `c * Y` -/
def mulUB (cl ch yl yh : ℚ) : ℚ := max (max (cl * yl) (cl * yh)) (max (ch * yl) (ch * yh))

lemma mulLB_le {cl ch yl yh c Y : ℝ} (hc1 : cl ≤ c) (hc2 : c ≤ ch) (hy1 : yl ≤ Y) (hy2 : Y ≤ yh) :
    min (min (cl * yl) (cl * yh)) (min (ch * yl) (ch * yh)) ≤ c * Y := by
  rcases le_total 0 Y with hY | hY
  · have h1 : cl * Y ≤ c * Y := mul_le_mul_of_nonneg_right hc1 hY
    rcases le_total 0 cl with hcl | hcl
    · have : cl * yl ≤ cl * Y := mul_le_mul_of_nonneg_left hy1 hcl
      exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (by linarith))
    · have : cl * yh ≤ cl * Y := mul_le_mul_of_nonpos_left hy2 hcl
      exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (by linarith))
  · have h1 : ch * Y ≤ c * Y := mul_le_mul_of_nonpos_right hc2 hY
    rcases le_total 0 ch with hch | hch
    · have : ch * yl ≤ ch * Y := mul_le_mul_of_nonneg_left hy1 hch
      exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (by linarith))
    · have : ch * yh ≤ ch * Y := mul_le_mul_of_nonpos_left hy2 hch
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (by linarith))

lemma le_mulUB {cl ch yl yh c Y : ℝ} (hc1 : cl ≤ c) (hc2 : c ≤ ch) (hy1 : yl ≤ Y) (hy2 : Y ≤ yh) :
    c * Y ≤ max (max (cl * yl) (cl * yh)) (max (ch * yl) (ch * yh)) := by
  rcases le_total 0 Y with hY | hY
  · have h1 : c * Y ≤ ch * Y := mul_le_mul_of_nonneg_right hc2 hY
    rcases le_total 0 ch with hch | hch
    · have : ch * Y ≤ ch * yh := mul_le_mul_of_nonneg_left hy2 hch
      exact le_trans (by linarith) (le_trans (le_max_right (ch * yl) (ch * yh)) (le_max_right _ _))
    · have : ch * Y ≤ ch * yl := mul_le_mul_of_nonpos_left hy1 hch
      exact le_trans (by linarith) (le_trans (le_max_left (ch * yl) (ch * yh)) (le_max_right _ _))
  · have h1 : c * Y ≤ cl * Y := mul_le_mul_of_nonpos_right hc1 hY
    rcases le_total 0 cl with hcl | hcl
    · have : cl * Y ≤ cl * yh := mul_le_mul_of_nonneg_left hy2 hcl
      exact le_trans (by linarith) (le_trans (le_max_right (cl * yl) (cl * yh)) (le_max_left _ _))
    · have : cl * Y ≤ cl * yl := mul_le_mul_of_nonpos_left hy1 hcl
      exact le_trans (by linarith) (le_trans (le_max_left (cl * yl) (cl * yh)) (le_max_left _ _))

/-- certified scaled cosine/sine enclosures at an integer angle -/
def cosLoQ (t : Int) : ℚ := (cosLo t : ℚ) / S
def cosHiQ (t : Int) : ℚ := (cosHi t : ℚ) / S
def sinLoQ (t : Int) : ℚ := (sinLo t : ℚ) / S
def sinHiQ (t : Int) : ℚ := (sinHi t : ℚ) / S

/-- lower bound of `cos (2π t/S) Y - sin (2π t/S) X` over `|X - x|, |Y - y| ≤ rb` -/
def cross1LB (t : Int) (x y rb : ℚ) : ℚ :=
  mulLB (cosLoQ t) (cosHiQ t) (y - rb) (y + rb) - mulUB (sinLoQ t) (sinHiQ t) (x - rb) (x + rb)
/-- lower bound of `X sin (2π t/S) - Y cos (2π t/S)` over the same box -/
def cross2LB (t : Int) (x y rb : ℚ) : ℚ :=
  mulLB (sinLoQ t) (sinHiQ t) (x - rb) (x + rb) - mulUB (cosLoQ t) (cosHiQ t) (y - rb) (y + rb)

/-- all bracket checks for point `p` -/
def brk16 (p : Nat) : Bool :=
  let x := n16K.utq (2 * p)
  let y := n16K.utq (2 * p + 1)
  let rb := n16K.rb
  let m := 2 * (|x| + |y|) * rb
  decide (0 ≤ r16Lo.getD p 0) && decide (0 ≤ r16Hi.getD p 0) &&
  decide (((r16Lo.getD p 0 : ℚ) / S) ^ 2 ≤ x ^ 2 + y ^ 2 - m) &&
  decide (x ^ 2 + y ^ 2 + m + 2 * rb ^ 2 ≤ ((r16Hi.getD p 0 : ℚ) / S) ^ 2) &&
  decide (a16Lo.getD p 0 ≤ a16Hi.getD p 0) && decide (2 * (a16Hi.getD p 0 - a16Lo.getD p 0) ≤ S) &&
  decide (0 < cross1LB (a16Lo.getD p 0) x y rb) && decide (0 < cross2LB (a16Hi.getD p 0) x y rb)

set_option maxRecDepth 100000 in
theorem brk16_all : (List.range 16).all brk16 = true := by decide +kernel

/-! ### Consequences of the bracket checks -/

lemma brk16_spec {p : ℕ} (hp : p < 16) : brk16 p = true := by
  have h := brk16_all
  rw [List.all_eq_true] at h
  exact h p (List.mem_range.mpr hp)

lemma n16_rb : (n16K.rb : ℝ) = 1 / 2 ^ 80 := by
  show ((1 / 2 ^ 80 : ℚ) : ℝ) = _; push_cast; ring

lemma u16_near {k : ℕ} (hk : k < 33) : |u16 k - (n16K.utq k : ℝ)| ≤ n16K.rb := u16_close k hk

lemma sq_lower {X x rb : ℝ} (h : |X - x| ≤ rb) : x ^ 2 - 2 * |x| * rb ≤ X ^ 2 := by
  have h1 : -rb ≤ X - x := (abs_le.mp h).1
  have h2 : X - x ≤ rb := (abs_le.mp h).2
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]; nlinarith [sq_nonneg (X - x)]
  · rw [abs_of_nonpos hx]; nlinarith [sq_nonneg (X - x)]

lemma sq_upper {X x rb : ℝ} (h : |X - x| ≤ rb) : X ^ 2 ≤ x ^ 2 + 2 * |x| * rb + rb ^ 2 := by
  have h1 : -rb ≤ X - x := (abs_le.mp h).1
  have h2 : X - x ≤ rb := (abs_le.mp h).2
  have hrb : 0 ≤ rb := le_trans (abs_nonneg _) h
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]; nlinarith
  · rw [abs_of_nonpos hx]; nlinarith

lemma norm_C16_sq (p : ℕ) : ‖C16 p‖ ^ 2 = u16 (2 * p) ^ 2 + u16 (2 * p + 1) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp [C16]; ring

/-- the radius bracket -/
lemma C16_radius {p : ℕ} (hp : p < 16) :
    sc (r16Lo.getD p 0) ≤ ‖C16 p‖ ∧ ‖C16 p‖ ≤ sc (r16Hi.getD p 0) := by
  have h := brk16_spec hp
  unfold brk16 at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h0'⟩, hlo⟩, hhi⟩, -⟩, -⟩, -⟩, -⟩ := h
  have hx := u16_near (k := 2 * p) (by omega)
  have hy := u16_near (k := 2 * p + 1) (by omega)
  set x := n16K.utq (2 * p)
  set y := n16K.utq (2 * p + 1)
  have hlo' := (Rat.cast_le (K := ℝ)).mpr hlo
  have hhi' := (Rat.cast_le (K := ℝ)).mpr hhi
  push_cast at hlo' hhi'
  have l1 := sq_lower hx
  have l2 := sq_lower hy
  have u1 := sq_upper hx
  have u2 := sq_upper hy
  have hS := S_pos
  have hn := norm_C16_sq p
  have hrl : (0 : ℝ) ≤ sc (r16Lo.getD p 0) := sc_nonneg h0
  constructor
  · have hsq : sc (r16Lo.getD p 0) ^ 2 ≤ ‖C16 p‖ ^ 2 := by
      rw [hn]; unfold sc
      have e : ((r16Lo.getD p 0 : ℝ) / S) ^ 2 = ((r16Lo.getD p 0 : ℚ) : ℝ) ^ 2 / (S : ℝ) ^ 2 := by
        push_cast; ring
      nlinarith
    exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) hsq
  · have hsq : ‖C16 p‖ ^ 2 ≤ sc (r16Hi.getD p 0) ^ 2 := by
      rw [hn]; unfold sc
      nlinarith
    exact le_of_pow_le_pow_left₀ two_ne_zero (sc_nonneg h0') hsq

/-- the angle bracket -/
lemma C16_angle {p : ℕ} (hp : p < 16) :
    ∃ m : ℤ, sc (a16Lo.getD p 0) < toTurn (C16 p) + m ∧ toTurn (C16 p) + m < sc (a16Hi.getD p 0) := by
  have h := brk16_spec hp
  unfold brk16 at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, h12⟩, h12'⟩, hc1⟩, hc2⟩ := h
  have hx := u16_near (k := 2 * p) (by omega)
  have hy := u16_near (k := 2 * p + 1) (by omega)
  set x := n16K.utq (2 * p)
  set y := n16K.utq (2 * p + 1)
  set rb := n16K.rb
  set t1 := a16Lo.getD p 0
  set t2 := a16Hi.getD p 0
  have hre : (C16 p).re = u16 (2 * p) := rfl
  have him : (C16 p).im = u16 (2 * p + 1) := rfl
  have hX1 : (x : ℝ) - rb ≤ u16 (2 * p) := by have := (abs_le.mp hx).1; linarith
  have hX2 : u16 (2 * p) ≤ (x : ℝ) + rb := by have := (abs_le.mp hx).2; linarith
  have hY1 : (y : ℝ) - rb ≤ u16 (2 * p + 1) := by have := (abs_le.mp hy).1; linarith
  have hY2 : u16 (2 * p + 1) ≤ (y : ℝ) + rb := by have := (abs_le.mp hy).2; linarith
  have cQ : ∀ t : ℤ, ((cosLoQ t : ℚ) : ℝ) = sc (cosLo t) ∧ ((cosHiQ t : ℚ) : ℝ) = sc (cosHi t) ∧
      ((sinLoQ t : ℚ) : ℝ) = sc (sinLo t) ∧ ((sinHiQ t : ℚ) : ℝ) = sc (sinHi t) := by
    intro t; refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [cosLoQ, cosHiQ, sinLoQ, sinHiQ, sc]
  apply angle_bracket
  · exact sc_le_iff.mpr h12
  · have := sc_le_iff.mpr h12'
    rw [show (2 : ℤ) * (t2 - t1) = (t2 - t1) + (t2 - t1) by ring, sc_add, sc_sub, sc_S] at this
    linarith
  · rw [him, hre]
    obtain ⟨e1, e2, e3, e4⟩ := cQ t1
    have hc := (Rat.cast_lt (K := ℝ)).mpr hc1
    simp only [cross1LB, mulLB, mulUB, Rat.cast_sub, Rat.cast_min, Rat.cast_max, Rat.cast_mul, Rat.cast_add,
      Rat.cast_zero, e1, e2, e3, e4] at hc
    have m1 := mulLB_le (cosLo_le t1) (cos_le_cosHi t1) hY1 hY2
    have m2 := le_mulUB (sinLo_le t1) (sin_le_sinHi t1) hX1 hX2
    linarith
  · rw [him, hre]
    obtain ⟨e1, e2, e3, e4⟩ := cQ t2
    have hc := (Rat.cast_lt (K := ℝ)).mpr hc2
    simp only [cross2LB, mulLB, mulUB, Rat.cast_sub, Rat.cast_min, Rat.cast_max, Rat.cast_mul, Rat.cast_add,
      Rat.cast_zero, e1, e2, e3, e4] at hc
    have m1 := mulLB_le (sinLo_le t2) (sin_le_sinHi t2) hX1 hX2
    have m2 := le_mulUB (cosLo_le t2) (cos_le_cosHi t2) hY1 hY2
    have e5 : u16 (2 * p) * Real.sin (2 * π * sc t2) = Real.sin (2 * π * sc t2) * u16 (2 * p) := mul_comm _ _
    have e6 : u16 (2 * p + 1) * Real.cos (2 * π * sc t2) = Real.cos (2 * π * sc t2) * u16 (2 * p + 1) :=
      mul_comm _ _
    linarith


/-! ### The container parameter of `c*` -/

def P16lo : ℚ := n16K.utq 32 - n16K.rb
def P16hi : ℚ := n16K.utq 32 + n16K.rb

lemma P16s_bounds : (P16lo : ℝ) ≤ P16s ∧ P16s ≤ (P16hi : ℝ) := by
  have h := u16_near (k := 32) (by norm_num)
  unfold P16s P16lo P16hi
  push_cast
  constructor <;> linarith [(abs_le.mp h).1, (abs_le.mp h).2]

/-- rational facts about `ρ*²` used below -/
def rho16OK : Bool :=
  decide ((2 + 1 / 1000000 : ℚ) ^ 2 < P16lo) &&
  decide (P16hi ≤ ((3975202480924 : ℚ) / S) ^ 2) &&
  decide (P16hi ≤ (rho2Hi16 : ℚ) / ((S : ℚ) * S))

set_option maxRecDepth 100000 in
theorem rho16OK_true : rho16OK = true := by decide +kernel

lemma P16s_pos : 0 < P16s := by
  have h := rho16OK_true
  unfold rho16OK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have h1 := (Rat.cast_lt (K := ℝ)).mpr h.1.1
  push_cast at h1
  have := P16s_bounds.1
  nlinarith

lemma ρ16_pos : 0 < ρ16 := Real.sqrt_pos.mpr P16s_pos
lemma ρ16_sq : ρ16 ^ 2 = P16s := Real.sq_sqrt P16s_pos.le

lemma two_lt_ρ16 : 2 + ((epsR : ℚ) : ℝ) < ρ16 := by
  have h := rho16OK_true
  unfold rho16OK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have h1 := (Rat.cast_lt (K := ℝ)).mpr h.1.1
  push_cast at h1
  have hb := P16s_bounds.1
  have heps : ((epsR : ℚ) : ℝ) = 1 / 1000000 := by unfold epsR; push_cast; ring
  rw [heps]
  have hsq : ((2 : ℝ) + 1 / 1000000) ^ 2 < ρ16 ^ 2 := by rw [ρ16_sq]; linarith
  exact lt_of_pow_lt_pow_left₀ 2 ρ16_pos.le hsq

lemma ρ16_le_P16 (k : ℕ) : ρ16 ≤ sc (P16 k).ρ := by
  have h := rho16OK_true
  unfold rho16OK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have h2 := (Rat.cast_le (K := ℝ)).mpr h.1.2
  push_cast at h2
  have hb := P16s_bounds.2
  have hS := S_pos
  have e : sc (P16 k).ρ = (3975202480924 : ℝ) / (S : ℝ) := by
    show sc 3975202480924 = _; unfold sc; push_cast; ring
  rw [e]
  have hsq : ρ16 ^ 2 ≤ ((3975202480924 : ℝ) / (S : ℝ)) ^ 2 := by rw [ρ16_sq]; linarith
  exact le_of_pow_le_pow_left₀ two_ne_zero (div_nonneg (by norm_num) hS.le) hsq

lemma ρ16_sq_le : ρ16 ^ 2 ≤ (rho2Hi16 : ℝ) / ((S : ℝ) * S) := by
  have h := rho16OK_true
  unfold rho16OK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have h3 := (Rat.cast_le (K := ℝ)).mpr h.2
  push_cast at h3
  rw [ρ16_sq]
  linarith [P16s_bounds.2]

/-- boundary points of `c*` lie on the circle of radius `ρ*` -/
lemma C16_bnd_norm {t : ℕ} (ht : t < 11) : ‖C16 (5 + t)‖ = ρ16 := by
  have h := C16_bnd ht
  have hb : n16K.bi t = 5 + t := by
    have : ∀ t < 11, n16K.bi t = 5 + t := by decide
    exact this t ht
  rw [hb] at h
  have hn := norm_C16_sq (5 + t)
  have hsq : ‖C16 (5 + t)‖ ^ 2 = ρ16 ^ 2 := by rw [hn, ρ16_sq, h]
  have := ρ16_pos
  nlinarith [norm_nonneg (C16 (5 + t)), sq_nonneg (‖C16 (5 + t)‖ - ρ16), sq_nonneg (‖C16 (5 + t)‖ + ρ16)]

end CirclePacking
