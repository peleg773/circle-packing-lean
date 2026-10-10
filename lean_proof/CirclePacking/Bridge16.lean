import CirclePacking.Main16
import CirclePacking.Tower16Real
import CirclePacking.Root16

/-!
# The 16-circle optimum `c*` in symmetric reduced form, and `H16(q) = 0`

1. `c*` is symmetric under the mirror `(x, y) ↦ (x, -y)` (by local uniqueness: its mirror image satisfies
   the same constraints and is within the uniqueness radius).
2. Its boundary centres form a chain: `c*_{p+1} = c*_p · v` with `v = q + i s`, `q = 1 - 2/ρ*²`,
   `s = √(1 - q²)`, so `c*_{10 ± m} = -ρ* v^{±m}`.
3. The five independent contacts then give the reduced system, and `H16(q) = 0` (`Tower16Real`).
4. Hence `q` is the largest real root `q16` of `H16` (`Root16`).
-/

open Real Finset

namespace CirclePacking

/-! ### Mirror symmetry -/

/-- the mirror permutation of the record configuration -/
def sig16 (p : ℕ) : ℕ := [0, 4, 3, 2, 1, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5].getD p 0

/-- `sig16` is an involution and the rational configuration `n16ut` is exactly mirror symmetric -/
def symOK16 : Bool := (List.range 16).all (fun p =>
  decide (sig16 p < 16) && decide (sig16 (sig16 p) = p) &&
  decide (n16K.utq (2 * sig16 p) = n16K.utq (2 * p)) &&
  decide (n16K.utq (2 * sig16 p + 1) = -n16K.utq (2 * p + 1)))

set_option maxRecDepth 100000 in
theorem symOK16_true : symOK16 = true := by decide +kernel

lemma sig16_spec {p : ℕ} (hp : p < 16) : sig16 p < 16 ∧ sig16 (sig16 p) = p ∧
    n16K.utq (2 * sig16 p) = n16K.utq (2 * p) ∧ n16K.utq (2 * sig16 p + 1) = -n16K.utq (2 * p + 1) := by
  have h := symOK16_true
  simp only [symOK16, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h p hp
  exact ⟨a, b, c, d⟩

/-- the mirror image of `c*` (coordinates `2p`, `2p+1`) -/
noncomputable def zmir (c : ℕ) : ℝ :=
  if c % 2 = 0 then u16 (2 * sig16 (c / 2)) else -u16 (2 * sig16 (c / 2) + 1)

lemma zmir_even (p : ℕ) : zmir (2 * p) = u16 (2 * sig16 p) := by
  simp [zmir, show 2 * p / 2 = p by omega]

lemma zmir_odd (p : ℕ) : zmir (2 * p + 1) = -u16 (2 * sig16 p + 1) := by
  simp only [zmir, show (2 * p + 1) % 2 = 1 by omega, show (2 * p + 1) / 2 = p by omega]; simp

lemma u16_sub_ut {k : ℕ} (hk : k < 33) : |u16 k - n16K.utq k| ≤ n16K.rb := u16_near hk

theorem u16_mirror : ∀ c < 32, zmir c = u16 c := by
  have hrb : (n16LU.rb : ℝ) = n16K.rb := rfl
  have hcs : ∀ c < 2 * n16LU.N, |u16 c - (n16LU.ctq c : ℝ)| ≤ n16LU.rb := by
    intro c hc
    have hc' : c < 32 := hc
    rw [n16LU_ctq hc']
    exact u16_near (by omega)
  have hcon : ∀ r < n16LU.nC, (u16 (2 * n16LU.ci r) - u16 (2 * n16LU.cj r)) ^ 2 +
      (u16 (2 * n16LU.ci r + 1) - u16 (2 * n16LU.cj r + 1)) ^ 2 = 4 :=
    fun r hr => C16_contact (r := r) hr
  have hbnd : ∀ t < n16LU.nB, u16 (2 * n16LU.bi t) ^ 2 + u16 (2 * n16LU.bi t + 1) ^ 2 = P16s :=
    fun t ht => C16_bnd (t := t) ht
  have hgc : u16 n16LU.gauge = 0 := C16_gauge
  have hpk := cstar16_packing
  have hzc : ∀ r < n16LU.nC, 4 ≤ (zmir (2 * n16LU.ci r) - zmir (2 * n16LU.cj r)) ^ 2 +
      (zmir (2 * n16LU.ci r + 1) - zmir (2 * n16LU.cj r + 1)) ^ 2 := by
    intro r hr
    have hcij : n16LU.ci r < 16 ∧ n16LU.cj r < 16 ∧ n16LU.ci r ≠ n16LU.cj r := by
      have : ∀ r < 21, n16LU.ci r < 16 ∧ n16LU.cj r < 16 ∧ n16LU.ci r ≠ n16LU.cj r := by decide
      exact this r hr
    obtain ⟨hi, hj, hij⟩ := hcij
    obtain ⟨si, ssi, -, -⟩ := sig16_spec hi
    obtain ⟨sj, ssj, -, -⟩ := sig16_spec hj
    have hne : sig16 (n16LU.ci r) ≠ sig16 (n16LU.cj r) := by
      intro h; apply hij; rw [← ssi, ← ssj, h]
    rw [zmir_even, zmir_even, zmir_odd, zmir_odd]
    have hd := dist_C16_sq (sig16 (n16LU.ci r)) (sig16 (n16LU.cj r))
    have h4 : 4 ≤ ‖C16 (sig16 (n16LU.ci r)) - C16 (sig16 (n16LU.cj r))‖ ^ 2 := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact C16_dist_ge si sj hlt
      · rw [norm_sub_rev]; exact C16_dist_ge sj si hgt
    rw [hd] at h4
    nlinarith
  have hzb : ∀ t < n16LU.nB, zmir (2 * n16LU.bi t) ^ 2 + zmir (2 * n16LU.bi t + 1) ^ 2 ≤ P16s := by
    intro t ht
    have hb : n16LU.bi t < 16 := by
      have : ∀ t < 11, n16LU.bi t < 16 := by decide
      exact this t ht
    obtain ⟨sb, -, -, -⟩ := sig16_spec hb
    rw [zmir_even, zmir_odd, neg_sq, ← norm_C16_sq, ← ρ16_sq]
    have := hpk.1 ⟨sig16 (n16LU.bi t), sb⟩
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  have hzg : zmir n16LU.gauge = 0 := by
    show zmir (2 * 0 + 1) = 0
    rw [zmir_odd, show sig16 0 = 0 from rfl]
    simp [C16_gauge]
  have hclose : ∑ c ∈ range (2 * n16LU.N), (zmir c - u16 c) ^ 2 < n16LU.R2 := by
    have hterm : ∀ c ∈ range (2 * n16LU.N), (zmir c - u16 c) ^ 2 ≤ (2 * (n16K.rb : ℝ)) ^ 2 := by
      intro c hc
      have hc' : c < 32 := Finset.mem_range.mp hc
      have hb : |zmir c - u16 c| ≤ 2 * (n16K.rb : ℝ) := by
        rcases Nat.even_or_odd' c with ⟨p, rfl | rfl⟩
        · obtain ⟨sp, -, hx, -⟩ := sig16_spec (show p < 16 by omega)
          rw [zmir_even]
          have a1 := u16_near (k := 2 * sig16 p) (by omega)
          have a2 := u16_near (k := 2 * p) (by omega)
          rw [hx] at a1
          calc |u16 (2 * sig16 p) - u16 (2 * p)| =
                |(u16 (2 * sig16 p) - n16K.utq (2 * p)) - (u16 (2 * p) - n16K.utq (2 * p))| := by ring_nf
            _ ≤ _ := abs_sub _ _
            _ ≤ _ := by linarith
        · obtain ⟨sp, -, -, hy⟩ := sig16_spec (show p < 16 by omega)
          rw [zmir_odd]
          have a1 := u16_near (k := 2 * sig16 p + 1) (by omega)
          have a2 := u16_near (k := 2 * p + 1) (by omega)
          rw [hy] at a1
          push_cast at a1
          calc |-u16 (2 * sig16 p + 1) - u16 (2 * p + 1)| =
                |-(u16 (2 * sig16 p + 1) - -(n16K.utq (2 * p + 1) : ℝ)) - (u16 (2 * p + 1) - n16K.utq (2 * p + 1))| := by
                ring_nf
            _ ≤ _ := abs_sub _ _
            _ ≤ _ := by rw [abs_neg]; linarith
      calc (zmir c - u16 c) ^ 2 = |zmir c - u16 c| ^ 2 := (sq_abs _).symm
        _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) hb 2
    refine lt_of_le_of_lt (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, show 2 * n16LU.N = 32 from rfl]
    have hR' : n16LU.R2 = (24 / 100000000 : ℚ) := by decide +kernel
    have hR : (n16LU.R2 : ℝ) = 24 / 100000000 := by rw [hR']; push_cast; ring
    rw [hR, n16_rb]
    norm_num
  exact local_unique_gen n16LU n16LU_ok u16 zmir P16s hcs hcon hbnd hgc hzc hzb hzg hclose

/-- **`c*` is mirror symmetric.** -/
theorem C16_mirror {p : ℕ} (hp : p < 16) : C16 (sig16 p) = (starRingEnd ℂ) (C16 p) := by
  have h1 := u16_mirror (2 * p) (by omega)
  have h2 := u16_mirror (2 * p + 1) (by omega)
  rw [zmir_even] at h1
  rw [zmir_odd] at h2
  apply Complex.ext
  · simp [C16, h1]
  · simp [C16]; linarith

/-! ### Consequences of the symmetry -/

lemma contact16 {r i j : ℕ} (hr : r < 21) (hi : n16K.ci r = i) (hj : n16K.cj r = j) :
    (u16 (2 * i) - u16 (2 * j)) ^ 2 + (u16 (2 * i + 1) - u16 (2 * j + 1)) ^ 2 = 4 := by
  have h := C16_contact hr
  rw [hi, hj] at h
  exact h

lemma bnd16 {t p : ℕ} (ht : t < 11) (hp : n16K.bi t = p) : u16 (2 * p) ^ 2 + u16 (2 * p + 1) ^ 2 = P16s := by
  have h := C16_bnd ht
  rw [hp] at h
  exact h

lemma u16_near' {k : ℕ} (hk : k < 33) :
    (n16K.utq k : ℝ) - 1 / 2 ^ 80 ≤ u16 k ∧ u16 k ≤ (n16K.utq k : ℝ) + 1 / 2 ^ 80 := by
  have h := u16_near hk
  rw [n16_rb] at h
  constructor <;> linarith [(abs_le.mp h).1, (abs_le.mp h).2]

/-- the mirror fixes the boundary point `10`: `c*_10 = (u16 20, 0)` -/
lemma u16_21 : u16 21 = 0 := by
  have h := congrArg Complex.im (C16_mirror (p := 10) (by norm_num))
  simp only [show sig16 10 = 10 from rfl, Complex.conj_im] at h
  simp only [C16] at h
  linarith

/-- the interior points `2, 3` touch and are mirror images: `c*_2 = (u16 4, 1)` -/
lemma u16_5 : u16 5 = 1 := by
  have h := C16_mirror (p := 2) (by norm_num)
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [show sig16 2 = 3 from rfl, Complex.conj_re, Complex.conj_im, C16] at hre him
  have hc := contact16 (r := 6) (i := 2) (j := 3) (by norm_num) rfl rfl
  norm_num at hre him hc
  rw [hre, him] at hc
  have h1 : u16 5 ^ 2 = 1 := by nlinarith
  have hpos := (u16_near' (k := 5) (by norm_num)).1
  have hu : (n16K.utq 5 : ℝ) = 1 := by
    have : n16K.utq 5 = 1 := by decide +kernel
    rw [this]; norm_num
  rw [hu] at hpos
  have hp : 0 < u16 5 := by linarith [show (1 : ℝ) / 2 ^ 80 < 1 by norm_num]
  nlinarith [sq_nonneg (u16 5 - 1), sq_nonneg (u16 5 + 1)]

/-- `c*_10 = (-ρ*, 0)` -/
lemma u16_20 : u16 20 = -ρ16 := by
  have hb := bnd16 (t := 5) (p := 10) (by norm_num) rfl
  rw [u16_21] at hb
  norm_num at hb
  have hneg : u16 20 < 0 := by
    have h := (u16_near' (k := 20) (by norm_num)).2
    have : (n16K.utq 20 : ℝ) < -3 := by
      have : n16K.utq 20 < -3 := by decide +kernel
      exact_mod_cast this
    linarith [show (1 : ℝ) / 2 ^ 80 < 1 by norm_num]
  have hρ := ρ16_pos
  have hsq : u16 20 ^ 2 = ρ16 ^ 2 := by rw [ρ16_sq]; linarith
  nlinarith [sq_nonneg (u16 20 + ρ16), sq_nonneg (u16 20 - ρ16)]

/-! ### The boundary step -/

/-- `q = cos θ` and `s = sin θ` of the boundary step -/
noncomputable def qg : ℝ := 1 - 2 / P16s
noncomputable def sg : ℝ := √(1 - qg ^ 2)

lemma P16s_qg : P16s * (1 - qg) = 2 := by
  have := P16s_pos
  unfold qg; field_simp; ring

lemma qg_bounds : (ql16 : ℝ) ≤ qg ∧ qg ≤ qh16 := by
  obtain ⟨h1, h2⟩ := P16s_bounds
  have hlo : (0 : ℝ) < P16lo := by
    have : (0 : ℚ) < P16lo := by decide +kernel
    exact_mod_cast this
  have hP := P16s_pos
  unfold qg ql16 qh16
  push_cast
  constructor
  · have : 2 / P16s ≤ 2 / (P16lo : ℝ) := div_le_div_of_nonneg_left (by norm_num) hlo h1
    linarith
  · have : 2 / (P16hi : ℝ) ≤ 2 / P16s := div_le_div_of_nonneg_left (by norm_num) hP h2
    linarith

lemma ql16_pos : (0 : ℝ) < ql16 := by
  have : (0 : ℚ) < ql16 := by decide +kernel
  exact_mod_cast this
lemma qh16_lt_one : (qh16 : ℝ) < 1 := by
  have : qh16 < 1 := by decide +kernel
  exact_mod_cast this

lemma qg_pos : 0 < qg := lt_of_lt_of_le ql16_pos qg_bounds.1
lemma qg_lt_one : qg < 1 := lt_of_le_of_lt qg_bounds.2 qh16_lt_one
lemma sg_sq : sg ^ 2 = 1 - qg ^ 2 := by
  unfold sg
  rw [Real.sq_sqrt]
  nlinarith [qg_pos, qg_lt_one]
lemma sg_pos : 0 < sg := by
  unfold sg
  apply Real.sqrt_pos.mpr
  nlinarith [qg_pos, qg_lt_one]

/-- a lower bound for `X Y` from enclosures of `X, Y` -/
lemma mul_lb {X x Y y e : ℝ} (hX : |X - x| ≤ e) (hY : |Y - y| ≤ e) :
    x * y - e * (|x| + |y|) - e ^ 2 ≤ X * Y := by
  have he : 0 ≤ e := le_trans (abs_nonneg _) hX
  have h1 : |X * Y - x * y| ≤ e * (|x| + |y|) + e ^ 2 := by
    have : X * Y - x * y = (X - x) * y + x * (Y - y) + (X - x) * (Y - y) := by ring
    rw [this]
    calc _ ≤ |(X - x) * y| + |x * (Y - y)| + |(X - x) * (Y - y)| := abs_add_three _ _ _
      _ = |X - x| * |y| + |x| * |Y - y| + |X - x| * |Y - y| := by rw [abs_mul, abs_mul, abs_mul]
      _ ≤ e * |y| + |x| * e + e * e := by gcongr
      _ = _ := by ring
  linarith [(abs_le.mp h1).1]

lemma mul_ub {X x Y y e : ℝ} (hX : |X - x| ≤ e) (hY : |Y - y| ≤ e) :
    X * Y ≤ x * y + e * (|x| + |y|) + e ^ 2 := by
  have := mul_lb (X := X) (x := x) (Y := -Y) (y := -y) (e := e) hX (by rw [show -Y - -y = -(Y - y) by ring, abs_neg]; exact hY)
  rw [abs_neg] at this
  linarith

/-- the cross products of consecutive boundary points are positive -/
def crossOK16 : Bool := (List.range 10).all (fun i =>
  let p := 5 + i
  let e := n16K.rb
  let x1 := n16K.utq (2 * p); let y1 := n16K.utq (2 * p + 1)
  let x2 := n16K.utq (2 * p + 2); let y2 := n16K.utq (2 * p + 3)
  decide (0 < (x1 * y2 - e * (|x1| + |y2|) - e ^ 2) - (y1 * x2 + e * (|y1| + |x2|) + e ^ 2)))

set_option maxRecDepth 100000 in
theorem crossOK16_true : crossOK16 = true := by decide +kernel

lemma cross_pos {p : ℕ} (h5 : 5 ≤ p) (h14 : p ≤ 14) :
    0 < u16 (2 * p) * u16 (2 * p + 3) - u16 (2 * p + 1) * u16 (2 * p + 2) := by
  have h := crossOK16_true
  simp only [crossOK16, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  have hc := h (p - 5) (by omega)
  rw [show 5 + (p - 5) = p by omega] at hc
  have hc' := (Rat.cast_lt (K := ℝ)).mpr hc
  push_cast at hc'
  have l1 := mul_lb (u16_near (k := 2 * p) (by omega)) (u16_near (k := 2 * p + 3) (by omega))
  have l2 := mul_ub (u16_near (k := 2 * p + 1) (by omega)) (u16_near (k := 2 * p + 2) (by omega))
  linarith

/-- **The boundary chain**: `c*_{p+1} = c*_p · (qg + i sg)` for `5 ≤ p ≤ 14` -/
lemma chain_step {p : ℕ} (h5 : 5 ≤ p) (h14 : p ≤ 14) :
    u16 (2 * p + 2) = u16 (2 * p) * qg - u16 (2 * p + 1) * sg ∧
    u16 (2 * p + 3) = u16 (2 * p) * sg + u16 (2 * p + 1) * qg := by
  set x1 := u16 (2 * p); set y1 := u16 (2 * p + 1)
  set x2 := u16 (2 * p + 2); set y2 := u16 (2 * p + 3)
  have h1 : x1 ^ 2 + y1 ^ 2 = P16s := by
    have hb : n16K.bi (p - 5) = p := by
      have : ∀ t < 11, n16K.bi t = 5 + t := by decide
      rw [this (p - 5) (by omega)]; omega
    exact bnd16 (t := p - 5) (by omega) hb
  have h2 : x2 ^ 2 + y2 ^ 2 = P16s := by
    have hb : n16K.bi (p - 4) = p + 1 := by
      have : ∀ t < 11, n16K.bi t = 5 + t := by decide
      rw [this (p - 4) (by omega)]; omega
    have := bnd16 (t := p - 4) (by omega) hb
    rwa [show 2 * (p + 1) = 2 * p + 2 by ring, show 2 * p + 2 + 1 = 2 * p + 3 by ring] at this
  have h3 : (x1 - x2) ^ 2 + (y1 - y2) ^ 2 = 4 := by
    have hci : n16K.ci (p + 6) = p := by
      have : ∀ r, 11 ≤ r → r < 21 → n16K.ci r = r - 6 := by decide
      rw [this (p + 6) (by omega) (by omega)]; omega
    have hcj : n16K.cj (p + 6) = p + 1 := by
      have : ∀ r, 11 ≤ r → r < 21 → n16K.cj r = r - 5 := by decide
      rw [this (p + 6) (by omega) (by omega)]; omega
    have := contact16 (r := p + 6) (by omega) hci hcj
    rwa [show 2 * (p + 1) = 2 * p + 2 by ring, show 2 * p + 2 + 1 = 2 * p + 3 by ring] at this
  have hcr := cross_pos h5 h14
  have hP := P16s_pos
  have hPq := P16s_qg
  have hs2 := sg_sq
  have hs := sg_pos
  have hdot : x1 * x2 + y1 * y2 = P16s * qg := by nlinarith
  have hcr2 : (x1 * y2 - y1 * x2) ^ 2 = (P16s * sg) ^ 2 := by
    have : (x1 * y2 - y1 * x2) ^ 2 + (x1 * x2 + y1 * y2) ^ 2 = (x1 ^ 2 + y1 ^ 2) * (x2 ^ 2 + y2 ^ 2) := by ring
    rw [h1, h2, hdot] at this
    rw [mul_pow, hs2]
    linarith
  have hcr' : x1 * y2 - y1 * x2 = P16s * sg := by
    have hpos : 0 < P16s * sg := mul_pos hP hs
    nlinarith [sq_nonneg (x1 * y2 - y1 * x2 - P16s * sg), sq_nonneg (x1 * y2 - y1 * x2 + P16s * sg)]
  constructor
  · have : P16s * x2 = P16s * (x1 * qg - y1 * sg) := by
      have e : (x1 ^ 2 + y1 ^ 2) * x2 = x1 * (x1 * x2 + y1 * y2) - y1 * (x1 * y2 - y1 * x2) := by ring
      rw [h1, hdot, hcr'] at e
      linarith
    exact mul_left_cancel₀ hP.ne' this
  · have : P16s * y2 = P16s * (x1 * sg + y1 * qg) := by
      have e : (x1 ^ 2 + y1 ^ 2) * y2 = y1 * (x1 * x2 + y1 * y2) + x1 * (x1 * y2 - y1 * x2) := by ring
      rw [h1, hdot, hcr'] at e
      linarith
    exact mul_left_cancel₀ hP.ne' this

/-! ### The chain in complex form -/

/-- the boundary step `v = qg + i sg` (`= e^{iθ}`) -/
noncomputable def v16 : ℂ := ⟨qg, sg⟩

lemma C16_succ {p : ℕ} (h5 : 5 ≤ p) (h14 : p ≤ 14) : C16 (p + 1) = C16 p * v16 := by
  obtain ⟨h1, h2⟩ := chain_step h5 h14
  apply Complex.ext
  · simp only [C16, v16, Complex.mul_re]
    rw [show 2 * (p + 1) = 2 * p + 2 by ring, h1]
  · simp only [C16, v16, Complex.mul_im]
    rw [show 2 * (p + 1) + 1 = 2 * p + 3 by ring, h2]

lemma C16_ten : C16 10 = -(ρ16 : ℂ) := by
  apply Complex.ext <;> simp [C16, u16_20, u16_21]

lemma C16_ten_add {m : ℕ} (hm : m ≤ 5) : C16 (10 + m) = -(ρ16 : ℂ) * v16 ^ m := by
  induction m with
  | zero => simp [C16_ten]
  | succ m ih =>
    rw [show 10 + (m + 1) = (10 + m) + 1 by ring, C16_succ (by omega) (by omega), ih (by omega), pow_succ]
    ring

lemma C16_ten_sub {m : ℕ} (hm : m ≤ 5) : C16 (10 - m) = -(ρ16 : ℂ) * (starRingEnd ℂ v16) ^ m := by
  have h := C16_mirror (p := 10 + m) (by omega)
  have hs : sig16 (10 + m) = 10 - m := by interval_cases m <;> rfl
  rw [hs, C16_ten_add hm] at h
  rw [h]; simp [map_mul, map_pow, map_neg, Complex.conj_ofReal]

lemma v16_pow3 : v16 ^ 3 = ⟨ZPoly.eval Tw16.zT3 qg, sg * ZPoly.eval Tw16.zU2 qg⟩ := by
  have hs := sg_sq
  apply Complex.ext
  · simp only [v16, pow_succ, pow_zero, one_mul, Complex.mul_re, Complex.mul_im, Tw16.zT3, ZPoly.eval]
    push_cast
    linear_combination (-3 * qg) * hs
  · simp only [v16, pow_succ, pow_zero, one_mul, Complex.mul_re, Complex.mul_im, Tw16.zU2, ZPoly.eval]
    push_cast
    linear_combination (-sg) * hs

lemma v16_pow5 : v16 ^ 5 = ⟨ZPoly.eval Tw16.zT5 qg, sg * ZPoly.eval Tw16.zU4 qg⟩ := by
  have hs := sg_sq
  apply Complex.ext
  · simp only [v16, pow_succ, pow_zero, one_mul, Complex.mul_re, Complex.mul_im, Tw16.zT5, ZPoly.eval]
    push_cast
    linear_combination (-5 * qg * (3 * qg ^ 2 - sg ^ 2 - 1)) * hs
  · simp only [v16, pow_succ, pow_zero, one_mul, Complex.mul_re, Complex.mul_im, Tw16.zU4, ZPoly.eval]
    push_cast
    linear_combination (-sg * (11 * qg ^ 2 - sg ^ 2 - 1)) * hs

/-- the boundary points touching the upper interior points -/
lemma u16_bnd5 : u16 10 = -(ρ16 * ZPoly.eval Tw16.zT5 qg) ∧ u16 11 = ρ16 * (sg * ZPoly.eval Tw16.zU4 qg) := by
  have h := C16_ten_sub (m := 5) (by norm_num)
  rw [show (10 : ℕ) - 5 = 5 from rfl, ← map_pow, v16_pow5] at h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [C16, Nat.reduceMul, Nat.reduceAdd, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im] at hre him
  exact ⟨by linear_combination hre, by linear_combination him⟩

lemma u16_bnd7 : u16 14 = -(ρ16 * ZPoly.eval Tw16.zT3 qg) ∧ u16 15 = ρ16 * (sg * ZPoly.eval Tw16.zU2 qg) := by
  have h := C16_ten_sub (m := 3) (by norm_num)
  rw [show (10 : ℕ) - 3 = 7 from rfl, ← map_pow, v16_pow3] at h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [C16, Nat.reduceMul, Nat.reduceAdd, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im] at hre him
  exact ⟨by linear_combination hre, by linear_combination him⟩

lemma u16_bnd9 : u16 18 = -(ρ16 * qg) ∧ u16 19 = ρ16 * sg := by
  have h := C16_ten_sub (m := 1) (by norm_num)
  rw [show (10 : ℕ) - 1 = 9 from rfl, pow_one] at h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [C16, v16, Nat.reduceMul, Nat.reduceAdd, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im] at hre him
  exact ⟨by linear_combination hre, by linear_combination him⟩

/-! ### The reduced system and `H16(q) = 0` -/

/-- `F16real` with its intermediate quantities named -/
lemma F16real_eq {q R t wa wd A D DD Nb : ℝ}
    (hA : A = -(R * ZPoly.eval Tw16.zT5 q) - (1 - q) * wa) (hD : D = -(R * q) + (1 - q) * wd)
    (hDD : DD = (A + R * ZPoly.eval Tw16.zT3 q) - (A - D) * t * ZPoly.eval Tw16.zU2 q)
    (hNb : Nb = (A * A - R * R) + t * ZPoly.eval Tw16.zU2 q * (D * D + (1 - q) * (1 - q) - A * A)) :
    Tw16.F16real q R t wa wd = (1 - q) * (1 - q) * ((2 * DD * A - Nb) * (2 * DD * A - Nb)) +
      ((A - D) * Nb + DD * (D * D + (1 - q) * (1 - q) - A * A)) *
      ((A - D) * Nb + DD * (D * D + (1 - q) * (1 - q) - A * A)) -
      16 * (1 - q) * (1 - q) * (1 - q) * (1 - q) * DD * DD := by
  subst hA hD hDD hNb; rfl

/-- the polynomial identity behind the elimination: with `2c = 2(a-d)b + d² + 1 - a²` and `2b·D = N`,
the scaled last contact equation is `4 L⁶ D² ((a - b)² + c² - 4)` -/
lemma F16_core {L a b c d Dd Nbb : ℝ} (E0 : (a - b) ^ 2 + c ^ 2 = 4)
    (hi : 2 * c = 2 * (a - d) * b + d ^ 2 + 1 - a ^ 2) (hii : 2 * b * Dd = Nbb) :
    L * L * ((2 * (L * Dd) * (L * a) - L ^ 2 * Nbb) * (2 * (L * Dd) * (L * a) - L ^ 2 * Nbb)) +
      ((L * a - L * d) * (L ^ 2 * Nbb) + L * Dd * (L * d * (L * d) + L * L - L * a * (L * a))) *
      ((L * a - L * d) * (L ^ 2 * Nbb) + L * Dd * (L * d * (L * d) + L * L - L * a * (L * a))) -
      16 * L * L * L * L * (L * Dd) * (L * Dd) = 0 := by
  linear_combination (4 * L ^ 6 * Dd ^ 2) * E0 +
    (L ^ 6 * (4 * Dd * (a - b) + (2 * b * Dd - Nbb) + (a - d) *
      (Dd * (2 * c - (2 * (a - d) * b + d ^ 2 + 1 - a ^ 2)) + (a - d) * (2 * b * Dd - Nbb) - 4 * c * Dd))) * hii +
    (L ^ 6 * Dd * (Dd * (2 * c - (2 * (a - d) * b + d ^ 2 + 1 - a ^ 2)) + (a - d) * (2 * b * Dd - Nbb) -
      4 * c * Dd)) * hi

/-- the algebraic core: the reduced contact equations force `F16real = 0` -/
lemma F16real_zero {q ρ s a b c d : ℝ} (hs : s ^ 2 = 1 - q ^ 2)
    (E0 : (a - b) ^ 2 + c ^ 2 = 4) (E1 : (b - d) ^ 2 + (c - 1) ^ 2 = 4)
    (E3 : (b + ρ * ZPoly.eval Tw16.zT3 q) ^ 2 + (c - ρ * s * ZPoly.eval Tw16.zU2 q) ^ 2 = 4) :
    Tw16.F16real q (ρ * (1 - q)) (ρ * s) (-a - ρ * ZPoly.eval Tw16.zT5 q) (d + ρ * q) = 0 := by
  have e3 : ZPoly.eval Tw16.zT3 q = 4 * q ^ 3 - 3 * q := by
    simp only [Tw16.zT3, ZPoly.eval]; push_cast; ring
  have eu2 : ZPoly.eval Tw16.zU2 q = 4 * q ^ 2 - 1 := by
    simp only [Tw16.zU2, ZPoly.eval]; push_cast; ring
  have hcheb : ZPoly.eval Tw16.zT3 q ^ 2 + s ^ 2 * ZPoly.eval Tw16.zU2 q ^ 2 = 1 := by
    rw [e3, eu2, hs]; ring
  have hi : 2 * c = 2 * (a - d) * b + d ^ 2 + 1 - a ^ 2 := by linear_combination E0 - E1
  have hii : 2 * b * (a + ρ * ZPoly.eval Tw16.zT3 q - (a - d) * (ρ * s) * ZPoly.eval Tw16.zU2 q) =
      a ^ 2 - ρ ^ 2 + (ρ * s) * ZPoly.eval Tw16.zU2 q * (d ^ 2 + 1 - a ^ 2) := by
    linear_combination E3 - E0 - ρ ^ 2 * hcheb + ρ * s * ZPoly.eval Tw16.zU2 q * hi
  rw [F16real_eq (A := (1 - q) * a) (D := (1 - q) * d)
    (DD := (1 - q) * (a + ρ * ZPoly.eval Tw16.zT3 q - (a - d) * (ρ * s) * ZPoly.eval Tw16.zU2 q))
    (Nb := (1 - q) ^ 2 * (a ^ 2 - ρ ^ 2 + (ρ * s) * ZPoly.eval Tw16.zU2 q * (d ^ 2 + 1 - a ^ 2)))
    (by ring) (by ring) (by ring) (by ring)]
  exact F16_core E0 hi hii

/-- **The optimum's `q` is a root of `H16`.** -/
theorem H16_qg : ZPoly.eval H16coeffs qg = 0 := by
  have hP := P16s_pos
  have hPq := P16s_qg
  have hs2 := sg_sq
  have hρ2 := ρ16_sq
  obtain ⟨h10, h11⟩ := u16_bnd5
  obtain ⟨h14, h15⟩ := u16_bnd7
  obtain ⟨h18, h19⟩ := u16_bnd9
  have hg := C16_gauge
  have h5 := u16_5
  -- the five contacts
  have c01 := contact16 (r := 0) (i := 0) (j := 1) (by norm_num) rfl rfl
  have c12 := contact16 (r := 4) (i := 1) (j := 2) (by norm_num) rfl rfl
  have c05 := contact16 (r := 2) (i := 0) (j := 5) (by norm_num) rfl rfl
  have c17 := contact16 (r := 5) (i := 1) (j := 7) (by norm_num) rfl rfl
  have c29 := contact16 (r := 7) (i := 2) (j := 9) (by norm_num) rfl rfl
  norm_num at c01 c12 c05 c17 c29
  rw [hg] at c01 c05
  rw [h5] at c12 c29
  rw [h10, h11] at c05
  rw [h14, h15] at c17
  rw [h18, h19] at c29
  have hT : Tw16.TowerRel qg (ρ16 * (1 - qg)) (ρ16 * sg) (-u16 0 - ρ16 * ZPoly.eval Tw16.zT5 qg) (u16 4 + ρ16 * qg) := by
    have h2 : ρ16 ^ 2 * (1 - qg) = 2 := by rw [hρ2]; exact hPq
    refine ⟨?_, ?_, ?_, ?_⟩
    · linear_combination (1 - qg) * h2
    · linear_combination (1 + qg) * h2 + ρ16 ^ 2 * hs2
    · have eu4 : ZPoly.eval Tw16.zU4 qg = 16 * qg ^ 4 - 12 * qg ^ 2 + 1 := by
        simp only [Tw16.zU4, ZPoly.eval]; push_cast; ring
      rw [eu4] at c05
      linear_combination c05 - (16 * qg ^ 4 - 12 * qg ^ 2 + 1) ^ 2 * ((1 + qg) * h2 + ρ16 ^ 2 * hs2)
    · linear_combination c29 - (1 + qg) * h2 - ρ16 ^ 2 * hs2
  have hF := F16real_zero (q := qg) (ρ := ρ16) (s := sg) (a := u16 0) (b := u16 2) (c := u16 3) (d := u16 4)
    hs2 (by linear_combination c01) (by linear_combination c12)
    (by linear_combination c17)
  exact Tw16.H16_eval_eq_zero hT hF qg_lt_one.ne (by linarith [qg_pos] : (0 : ℝ) < 1 + 2 * qg).ne'

/-- **`q16 = qg`**: the optimum's boundary step is the largest real root of `H16`. -/
theorem q16_eq_qg : q16 = qg := q16_eq_of_root qg_bounds H16_qg

/-- the optimal container parameter, from `q16` -/
theorem ρ16_eq : ρ16 = √(2 / (1 - q16)) := by
  rw [q16_eq_qg]
  have hP := P16s_pos
  have hPq := P16s_qg
  have h1 : 2 / (1 - qg) = P16s := by
    rw [div_eq_iff (by linarith [qg_lt_one])]; exact hPq.symm
  rw [h1]; rfl

end CirclePacking
