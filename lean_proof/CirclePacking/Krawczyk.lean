import Mathlib

/-!
# An exact solution of a contact system near an approximate one (generic)

Unknowns: `n = 2N + 1` reals `u`: the `2N` coordinates of `N` points (`2p`, `2p+1`) and `u_{2N} = P`
(the squared container radius).  Equations (`n` of them, in this order): the contact equations
`|x_i - x_j|² - 4 = 0` for the pairs in `ctc`, the boundary equations `|x_b|² - P = 0` for `bnd`, and the gauge
equation `u_g = 0`.  We need `ctc.length + bnd.length + 1 = n`.

Given a rational approximate solution `ũ` and a rational approximate inverse `A` of the Jacobian `J(ũ)`,
the checks below (exact rational arithmetic) show that the Newton map `T u = u - A F(u)` maps the box
`‖u - ũ‖∞ ≤ rb` into itself and is a contraction there.  Banach's fixed-point theorem then gives
`u*` in the box with `A F(u*) = 0`, and the check `‖I - J(ũ) A‖∞ < 1` makes `A` injective, so
`F(u*) = 0`.  For quadratic `F` the key identity is `F(u) - F(v) = J((u + v)/2) (u - v)`.
-/

open Finset

namespace CirclePacking

/-- data of an existence certificate -/
structure KData where
  N : ℕ
  ctc : List (ℕ × ℕ)
  bnd : List ℕ
  gauge : ℕ
  /-- the approximate solution (`2N` coordinates, then `P`) -/
  ut : List ℚ
  /-- the approximate inverse of the Jacobian (rows: unknowns; columns: equations) -/
  A : List (List ℚ)
  /-- the box radius (sup norm) -/
  rb : ℚ

namespace KData

variable (d : KData)

def n : ℕ := 2 * d.N + 1
def nC : ℕ := d.ctc.length
def nB : ℕ := d.bnd.length
def ci (r : ℕ) : ℕ := (d.ctc.getD r (0, 0)).1
def cj (r : ℕ) : ℕ := (d.ctc.getD r (0, 0)).2
def bi (t : ℕ) : ℕ := d.bnd.getD t 0
def utq (k : ℕ) : ℚ := d.ut.getD k 0
def Aq (k r : ℕ) : ℚ := (d.A.getD k []).getD r 0

/-- the equations at a real vector `u` -/
noncomputable def F (u : ℕ → ℝ) (r : ℕ) : ℝ :=
  if r < d.nC then
    (u (2 * d.ci r) - u (2 * d.cj r)) ^ 2 + (u (2 * d.ci r + 1) - u (2 * d.cj r + 1)) ^ 2 - 4
  else if r < d.nC + d.nB then
    u (2 * d.bi (r - d.nC)) ^ 2 + u (2 * d.bi (r - d.nC) + 1) ^ 2 - u (2 * d.N)
  else u d.gauge

/-- the Jacobian at a vector `m` (row `r`, column `k`), as a function of `m` -/
noncomputable def J (m : ℕ → ℝ) (r k : ℕ) : ℝ :=
  if r < d.nC then
    (if k = 2 * d.ci r then 2 * (m (2 * d.ci r) - m (2 * d.cj r)) else 0) +
    (if k = 2 * d.ci r + 1 then 2 * (m (2 * d.ci r + 1) - m (2 * d.cj r + 1)) else 0) +
    (if k = 2 * d.cj r then -(2 * (m (2 * d.ci r) - m (2 * d.cj r))) else 0) +
    (if k = 2 * d.cj r + 1 then -(2 * (m (2 * d.ci r + 1) - m (2 * d.cj r + 1))) else 0)
  else if r < d.nC + d.nB then
    (if k = 2 * d.bi (r - d.nC) then 2 * m (2 * d.bi (r - d.nC)) else 0) +
    (if k = 2 * d.bi (r - d.nC) + 1 then 2 * m (2 * d.bi (r - d.nC) + 1) else 0) +
    (if k = 2 * d.N then -1 else 0)
  else if k = d.gauge then 1 else 0

/-- the rational Jacobian at `ũ` -/
def Jq (r k : ℕ) : ℚ :=
  if r < d.nC then
    (if k = 2 * d.ci r then 2 * (d.utq (2 * d.ci r) - d.utq (2 * d.cj r)) else 0) +
    (if k = 2 * d.ci r + 1 then 2 * (d.utq (2 * d.ci r + 1) - d.utq (2 * d.cj r + 1)) else 0) +
    (if k = 2 * d.cj r then -(2 * (d.utq (2 * d.ci r) - d.utq (2 * d.cj r))) else 0) +
    (if k = 2 * d.cj r + 1 then -(2 * (d.utq (2 * d.ci r + 1) - d.utq (2 * d.cj r + 1))) else 0)
  else if r < d.nC + d.nB then
    (if k = 2 * d.bi (r - d.nC) then 2 * d.utq (2 * d.bi (r - d.nC)) else 0) +
    (if k = 2 * d.bi (r - d.nC) + 1 then 2 * d.utq (2 * d.bi (r - d.nC) + 1) else 0) +
    (if k = 2 * d.N then -1 else 0)
  else if k = d.gauge then 1 else 0

/-- the rational equations at `ũ` -/
def Fq (r : ℕ) : ℚ :=
  if r < d.nC then
    (d.utq (2 * d.ci r) - d.utq (2 * d.cj r)) ^ 2 + (d.utq (2 * d.ci r + 1) - d.utq (2 * d.cj r + 1)) ^ 2 - 4
  else if r < d.nC + d.nB then
    d.utq (2 * d.bi (r - d.nC)) ^ 2 + d.utq (2 * d.bi (r - d.nC) + 1) ^ 2 - d.utq (2 * d.N)
  else d.utq d.gauge

/-- `‖I - A J(ũ)‖∞` -/
def q0 : ℚ := (List.range d.n).foldl (fun acc k =>
  max acc (∑ l ∈ range d.n, |(if k = l then 1 else 0) - ∑ r ∈ range d.n, d.Aq k r * d.Jq r l|)) 0
/-- `‖A‖∞` -/
def normA : ℚ := (List.range d.n).foldl (fun acc k => max acc (∑ r ∈ range d.n, |d.Aq k r|)) 0
/-- `‖A F(ũ)‖∞` -/
def normAF : ℚ := (List.range d.n).foldl (fun acc k => max acc |∑ r ∈ range d.n, d.Aq k r * d.Fq r|) 0
/-- `‖I - J(ũ) A‖∞` -/
def q1 : ℚ := (List.range d.n).foldl (fun acc r =>
  max acc (∑ s ∈ range d.n, |(if r = s then 1 else 0) - ∑ k ∈ range d.n, d.Jq r k * d.Aq k s|)) 0
/-- the contraction constant on the box -/
def qq : ℚ := d.q0 + 16 * d.rb * d.normA

/-- all checks -/
def ok : Bool :=
  decide (d.nC + d.nB + 1 = d.n) && decide (d.gauge < 2 * d.N) &&
  (List.range d.nC).all (fun r => decide (d.ci r < d.N) && decide (d.cj r < d.N)) &&
  (List.range d.nB).all (fun t => decide (d.bi t < d.N)) &&
  decide (0 < d.rb) && decide (d.qq < 1) && decide (d.normAF ≤ (1 - d.qq) * d.rb) && decide (d.q1 < 1)

end KData


namespace KData

variable {d : KData}

lemma ok_spec (h : d.ok = true) :
    d.nC + d.nB + 1 = d.n ∧ d.gauge < 2 * d.N ∧ (∀ r < d.nC, d.ci r < d.N ∧ d.cj r < d.N) ∧
    (∀ t < d.nB, d.bi t < d.N) ∧ 0 < d.rb ∧ d.qq < 1 ∧ d.normAF ≤ (1 - d.qq) * d.rb ∧ d.q1 < 1 := by
  unfold ok at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- the foldl-max of a list of rationals bounds each term -/
lemma le_foldl_max (n : ℕ) (f : ℕ → ℚ) {k : ℕ} (hk : k < n) :
    f k ≤ (List.range n).foldl (fun acc i => max acc (f i)) 0 := by
  have key : ∀ (l : List ℕ) (a : ℚ), k ∈ l → f k ≤ l.foldl (fun acc i => max acc (f i)) a := by
    intro l
    induction l with
    | nil => intro a h; simp at h
    | cons x l ih =>
      intro a h
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp h with rfl | h'
      · have mono : ∀ (l : List ℕ) (b : ℚ), b ≤ l.foldl (fun acc i => max acc (f i)) b := by
          intro l
          induction l with
          | nil => intro b; simp
          | cons y l ih2 => intro b; simp only [List.foldl_cons]; exact le_trans (le_max_left _ _) (ih2 _)
        exact le_trans (le_max_right _ _) (mono l _)
      · exact ih _ h'
  exact key _ 0 (List.mem_range.mpr hk)

end KData


namespace KData

variable {d : KData}

lemma sum_ite_mul' {n a : ℕ} (ha : a < n) (x : ℝ) (w : ℕ → ℝ) :
    ∑ l ∈ range n, (if l = a then x else 0) * w l = x * w a := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_range.mpr ha) h

/-- `F(u) - F(v) = J((u+v)/2) (u - v)` (exact, since `F` is quadratic) -/
lemma F_sub (hn : d.nC + d.nB + 1 = d.n) (hg : d.gauge < 2 * d.N)
    (hC : ∀ r < d.nC, d.ci r < d.N ∧ d.cj r < d.N) (hB : ∀ t < d.nB, d.bi t < d.N)
    (u v : ℕ → ℝ) {r : ℕ} (hr : r < d.n) :
    d.F u r - d.F v r = ∑ l ∈ range d.n, d.J (fun k => (u k + v k) / 2) r l * (u l - v l) := by
  have hnN : d.n = 2 * d.N + 1 := rfl
  by_cases h1 : r < d.nC
  · obtain ⟨hi, hj⟩ := hC r h1
    simp only [F, J, if_pos h1, add_mul, Finset.sum_add_distrib]
    rw [sum_ite_mul' (by omega), sum_ite_mul' (by omega), sum_ite_mul' (by omega), sum_ite_mul' (by omega)]
    ring
  · by_cases h2 : r < d.nC + d.nB
    · have hb := hB (r - d.nC) (by omega)
      simp only [F, J, if_neg h1, if_pos h2, add_mul, Finset.sum_add_distrib]
      rw [sum_ite_mul' (by omega), sum_ite_mul' (by omega), sum_ite_mul' (by omega)]
      ring
    · simp only [F, J, if_neg h1, if_neg h2]
      rw [sum_ite_mul' (by omega)]
      ring

/-- each row of `J(m) - J(ũ)` acts with norm at most `16 rb` on the box -/
lemma J_sub_bound (hn : d.nC + d.nB + 1 = d.n) (hg : d.gauge < 2 * d.N)
    (hC : ∀ r < d.nC, d.ci r < d.N ∧ d.cj r < d.N) (hB : ∀ t < d.nB, d.bi t < d.N)
    (m : ℕ → ℝ) (hm : ∀ k < d.n, |m k - d.utq k| ≤ d.rb) (w : ℕ → ℝ) {W : ℝ}
    (hw : ∀ k < d.n, |w k| ≤ W) {r : ℕ} (hr : r < d.n) :
    |∑ l ∈ range d.n, (d.J m r l - d.Jq r l) * w l| ≤ 16 * d.rb * W := by
  have hnN : d.n = 2 * d.N + 1 := rfl
  have hW : 0 ≤ W := le_trans (abs_nonneg _) (hw 0 (by omega))
  have hrb : (0 : ℝ) ≤ d.rb := le_trans (abs_nonneg _) (hm 0 (by omega))
  by_cases h1 : r < d.nC
  · obtain ⟨hi, hj⟩ := hC r h1
    have e : ∑ l ∈ range d.n, (d.J m r l - d.Jq r l) * w l =
        2 * ((m (2 * d.ci r) - d.utq (2 * d.ci r)) - (m (2 * d.cj r) - d.utq (2 * d.cj r))) *
          (w (2 * d.ci r) - w (2 * d.cj r)) +
        2 * ((m (2 * d.ci r + 1) - d.utq (2 * d.ci r + 1)) - (m (2 * d.cj r + 1) - d.utq (2 * d.cj r + 1))) *
          (w (2 * d.ci r + 1) - w (2 * d.cj r + 1)) := by
      simp only [J, Jq, if_pos h1, Rat.cast_add, apply_ite (fun q : ℚ => (q : ℝ)), Rat.cast_zero, sub_mul,
        add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [sum_ite_mul' (by omega), sum_ite_mul' (by omega), sum_ite_mul' (by omega), sum_ite_mul' (by omega),
        sum_ite_mul' (by omega), sum_ite_mul' (by omega), sum_ite_mul' (by omega), sum_ite_mul' (by omega)]
      push_cast
      ring
    rw [e]
    have a1 := hm (2 * d.ci r) (by omega)
    have a2 := hm (2 * d.cj r) (by omega)
    have a3 := hm (2 * d.ci r + 1) (by omega)
    have a4 := hm (2 * d.cj r + 1) (by omega)
    have b1 := hw (2 * d.ci r) (by omega)
    have b2 := hw (2 * d.cj r) (by omega)
    have b3 := hw (2 * d.ci r + 1) (by omega)
    have b4 := hw (2 * d.cj r + 1) (by omega)
    have t1 : |2 * ((m (2 * d.ci r) - d.utq (2 * d.ci r)) - (m (2 * d.cj r) - d.utq (2 * d.cj r))) *
        (w (2 * d.ci r) - w (2 * d.cj r))| ≤ 2 * (2 * d.rb) * (2 * W) := by
      rw [abs_mul, abs_mul, abs_two]
      gcongr
      · exact le_trans (abs_sub _ _) (by linarith)
      · exact le_trans (abs_sub _ _) (by linarith)
    have t2 : |2 * ((m (2 * d.ci r + 1) - d.utq (2 * d.ci r + 1)) - (m (2 * d.cj r + 1) - d.utq (2 * d.cj r + 1))) *
        (w (2 * d.ci r + 1) - w (2 * d.cj r + 1))| ≤ 2 * (2 * d.rb) * (2 * W) := by
      rw [abs_mul, abs_mul, abs_two]
      gcongr
      · exact le_trans (abs_sub _ _) (by linarith)
      · exact le_trans (abs_sub _ _) (by linarith)
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ 16 * d.rb * W := by nlinarith
  · by_cases h2 : r < d.nC + d.nB
    · have hb := hB (r - d.nC) (by omega)
      have e : ∑ l ∈ range d.n, (d.J m r l - d.Jq r l) * w l =
          2 * (m (2 * d.bi (r - d.nC)) - d.utq (2 * d.bi (r - d.nC))) * w (2 * d.bi (r - d.nC)) +
          2 * (m (2 * d.bi (r - d.nC) + 1) - d.utq (2 * d.bi (r - d.nC) + 1)) * w (2 * d.bi (r - d.nC) + 1) := by
        simp only [J, Jq, if_neg h1, if_pos h2, Rat.cast_add, apply_ite (fun q : ℚ => (q : ℝ)), Rat.cast_zero,
          sub_mul, add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
        rw [sum_ite_mul' (by omega), sum_ite_mul' (by omega), sum_ite_mul' (by omega),
          sum_ite_mul' (by omega), sum_ite_mul' (by omega), sum_ite_mul' (by omega)]
        push_cast
        ring
      rw [e]
      have a1 := hm (2 * d.bi (r - d.nC)) (by omega)
      have a3 := hm (2 * d.bi (r - d.nC) + 1) (by omega)
      have b1 := hw (2 * d.bi (r - d.nC)) (by omega)
      have b3 := hw (2 * d.bi (r - d.nC) + 1) (by omega)
      have t1 : |2 * (m (2 * d.bi (r - d.nC)) - d.utq (2 * d.bi (r - d.nC))) * w (2 * d.bi (r - d.nC))| ≤
          2 * d.rb * W := by
        rw [abs_mul, abs_mul, abs_two]; gcongr
      have t3 : |2 * (m (2 * d.bi (r - d.nC) + 1) - d.utq (2 * d.bi (r - d.nC) + 1)) *
          w (2 * d.bi (r - d.nC) + 1)| ≤ 2 * d.rb * W := by
        rw [abs_mul, abs_mul, abs_two]; gcongr
      calc _ ≤ _ := abs_add_le _ _
        _ ≤ 16 * d.rb * W := by nlinarith
    · have e : ∑ l ∈ range d.n, (d.J m r l - d.Jq r l) * w l = 0 := by
        apply Finset.sum_eq_zero
        intro l _
        simp only [J, Jq, if_neg h1, if_neg h2]
        split_ifs <;> simp
      rw [e, abs_zero]
      positivity

end KData


/-! ### The existence theorem -/

namespace KData

variable {d : KData}

lemma foldl_max_nonneg (n : ℕ) (f : ℕ → ℚ) : 0 ≤ (List.range n).foldl (fun acc i => max acc (f i)) 0 := by
  have mono : ∀ (l : List ℕ) (b : ℚ), b ≤ l.foldl (fun acc i => max acc (f i)) b := by
    intro l
    induction l with
    | nil => intro b; simp
    | cons y l ih2 => intro b; simp only [List.foldl_cons]; exact le_trans (le_max_left _ _) (ih2 _)
  exact mono _ 0

end KData

open KData in
/-- **Existence of an exact solution near the approximate one.** -/
theorem exists_solution (d : KData) (hok : d.ok = true) :
    ∃ u : ℕ → ℝ, (∀ k < d.n, |u k - d.utq k| ≤ d.rb) ∧ ∀ r < d.n, d.F u r = 0 := by
  classical
  obtain ⟨hn, hg, hC, hB, hrb, hqq, hAF, hq1⟩ := KData.ok_spec hok
  have hnN : d.n = 2 * d.N + 1 := rfl
  have hn0 : 0 < d.n := by omega
  set n := d.n with hndef
  -- vectors
  let E : (Fin n → ℝ) → ℕ → ℝ := fun v k => if h : k < n then v ⟨k, h⟩ else 0
  have hE : ∀ (v : Fin n → ℝ) (k : Fin n), E v k = v k := by
    intro v k; simp [E, k.isLt]
  let T : (Fin n → ℝ) → (Fin n → ℝ) := fun v k => v k - ∑ r ∈ range n, (d.Aq k r : ℝ) * d.F (E v) r
  let c : Fin n → ℝ := fun k => (d.utq k : ℝ)
  set s := Metric.closedBall c (d.rb : ℝ) with hs
  have hrbR : (0 : ℝ) < d.rb := by exact_mod_cast hrb
  have hmem : ∀ v : Fin n → ℝ, v ∈ s ↔ ∀ k : Fin n, |v k - d.utq k| ≤ d.rb := by
    intro v
    rw [hs, Metric.mem_closedBall, dist_pi_le_iff hrbR.le]
    simp only [Real.dist_eq, c]
  -- rational quantities as reals
  have hq0 : ∀ k < n, (∑ l ∈ range n, |(if k = l then (1 : ℝ) else 0) - ∑ r ∈ range n, (d.Aq k r : ℝ) * d.Jq r l|)
      ≤ d.q0 := by
    intro k hk
    have h0 : (∑ l ∈ range n, |(if k = l then 1 else 0) - ∑ r ∈ range n, d.Aq k r * d.Jq r l| : ℚ) ≤ d.q0 :=
      le_foldl_max n (fun k => ∑ l ∈ range n, |(if k = l then 1 else 0) - ∑ r ∈ range n, d.Aq k r * d.Jq r l|) hk
    have h' : ((∑ l ∈ range n, |(if k = l then 1 else 0) - ∑ r ∈ range n, d.Aq k r * d.Jq r l| : ℚ) : ℝ) ≤
        (d.q0 : ℝ) := by exact_mod_cast h0
    push_cast at h'
    convert h' using 3
    split_ifs <;> simp
  have hnA : ∀ k < n, (∑ r ∈ range n, |(d.Aq k r : ℝ)|) ≤ d.normA := by
    intro k hk
    have := le_foldl_max n (fun k => ∑ r ∈ range n, |d.Aq k r|) hk
    have h' : ((∑ r ∈ range n, |d.Aq k r| : ℚ) : ℝ) ≤ (d.normA : ℝ) := by exact_mod_cast this
    push_cast at h'
    exact h'
  have hq0n : (0 : ℝ) ≤ d.q0 := by exact_mod_cast foldl_max_nonneg _ _
  have hnAn : (0 : ℝ) ≤ d.normA := by exact_mod_cast foldl_max_nonneg _ _
  have hqqR : (d.qq : ℝ) = d.q0 + 16 * d.rb * d.normA := by simp only [qq]; push_cast; ring
  have hqq0 : (0 : ℝ) ≤ d.qq := by rw [hqqR]; positivity
  have hqq1 : (d.qq : ℝ) < 1 := by exact_mod_cast hqq
  -- the contraction estimate
  have hlip : ∀ u ∈ s, ∀ v ∈ s, ∀ k : Fin n, |T u k - T v k| ≤ d.qq * dist u v := by
    intro u hu v hv k
    have hu' := (hmem u).mp hu
    have hv' := (hmem v).mp hv
    set w : ℕ → ℝ := fun l => E u l - E v l with hw
    set m : ℕ → ℝ := fun l => (E u l + E v l) / 2 with hm
    have hwD : ∀ l < n, |w l| ≤ dist u v := by
      intro l hl
      simp only [hw, E, dif_pos hl]
      rw [← Real.dist_eq]
      exact dist_le_pi_dist u v ⟨l, hl⟩
    have hmB : ∀ l < n, |m l - d.utq l| ≤ d.rb := by
      intro l hl
      have h1 := hu' ⟨l, hl⟩
      have h2 := hv' ⟨l, hl⟩
      simp only [hm, E, dif_pos hl]
      rw [abs_le] at h1 h2 ⊢
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    have hk : (k : ℕ) < n := k.isLt
    -- T u k - T v k = Σ_l (δ - A J̃) w - Σ_r A (J(m) - J̃) w
    have hdiff : T u k - T v k =
        ∑ l ∈ range n, ((if (k : ℕ) = l then (1 : ℝ) else 0) - ∑ r ∈ range n, (d.Aq k r : ℝ) * d.Jq r l) * w l -
        ∑ r ∈ range n, (d.Aq k r : ℝ) * ∑ l ∈ range n, (d.J m r l - d.Jq r l) * w l := by
      have hwk : u k - v k = ∑ l ∈ range n, (if (k : ℕ) = l then (1 : ℝ) else 0) * w l := by
        rw [Finset.sum_eq_single (k : ℕ)]
        · simp [hw, hE]
        · intro b _ hb; simp [Ne.symm hb]
        · intro h; exact absurd (Finset.mem_range.mpr hk) h
      have hF : ∀ r ∈ range n, d.F (E u) r - d.F (E v) r = ∑ l ∈ range n, d.J m r l * w l := by
        intro r hr
        exact F_sub hn hg hC hB (E u) (E v) (Finset.mem_range.mp hr)
      simp only [T]
      have hsplit : ∑ r ∈ range n, (d.Aq k r : ℝ) * (d.F (E u) r - d.F (E v) r) =
          ∑ r ∈ range n, (d.Aq k r : ℝ) * d.F (E u) r - ∑ r ∈ range n, (d.Aq k r : ℝ) * d.F (E v) r := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro r _; ring
      rw [show u k - ∑ r ∈ range n, (d.Aq k r : ℝ) * d.F (E u) r - (v k - ∑ r ∈ range n, (d.Aq k r : ℝ) * d.F (E v) r)
          = (u k - v k) - ∑ r ∈ range n, (d.Aq k r : ℝ) * (d.F (E u) r - d.F (E v) r) by
            rw [hsplit]; ring]
      have hsum2 : ∑ r ∈ range n, (d.Aq k r : ℝ) * (d.F (E u) r - d.F (E v) r) =
          ∑ r ∈ range n, (d.Aq k r : ℝ) * ∑ l ∈ range n, d.J m r l * w l :=
        Finset.sum_congr rfl (fun r hr => by rw [hF r hr])
      have hswap : ∑ l ∈ range n, (∑ r ∈ range n, (d.Aq k r : ℝ) * d.Jq r l) * w l =
          ∑ r ∈ range n, (d.Aq k r : ℝ) * ∑ l ∈ range n, (d.Jq r l : ℝ) * w l := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro r _
        apply Finset.sum_congr rfl; intro l _
        ring
      have hJsplit : ∑ r ∈ range n, (d.Aq k r : ℝ) * ∑ l ∈ range n, (d.J m r l - d.Jq r l) * w l =
          ∑ r ∈ range n, (d.Aq k r : ℝ) * ∑ l ∈ range n, d.J m r l * w l -
            ∑ r ∈ range n, (d.Aq k r : ℝ) * ∑ l ∈ range n, (d.Jq r l : ℝ) * w l := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro r _
        rw [← mul_sub, ← Finset.sum_sub_distrib]
        congr 1
        apply Finset.sum_congr rfl; intro l _
        ring
      have hδsum : ∑ l ∈ range n, ((if (k : ℕ) = l then (1 : ℝ) else 0) -
            ∑ r ∈ range n, (d.Aq k r : ℝ) * d.Jq r l) * w l =
          ∑ l ∈ range n, (if (k : ℕ) = l then (1 : ℝ) else 0) * w l -
            ∑ l ∈ range n, (∑ r ∈ range n, (d.Aq k r : ℝ) * d.Jq r l) * w l := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro l _
        ring
      rw [hsum2, hδsum, hJsplit, hswap, ← hwk]
      ring
    rw [hdiff]
    have b1 : |∑ l ∈ range n, ((if (k : ℕ) = l then (1 : ℝ) else 0) -
        ∑ r ∈ range n, (d.Aq k r : ℝ) * d.Jq r l) * w l| ≤ d.q0 * dist u v := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_sum (fun l hl => (show |((if (k : ℕ) = l then (1 : ℝ) else 0) -
          ∑ r ∈ range n, (d.Aq k r : ℝ) * d.Jq r l) * w l| ≤ |(if (k : ℕ) = l then (1 : ℝ) else 0) -
          ∑ r ∈ range n, (d.Aq k r : ℝ) * d.Jq r l| * dist u v from by
            rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hwD l (Finset.mem_range.mp hl)) (abs_nonneg _)))) ?_
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (hq0 k hk) dist_nonneg
    have b2 : |∑ r ∈ range n, (d.Aq k r : ℝ) * ∑ l ∈ range n, (d.J m r l - d.Jq r l) * w l| ≤
        16 * d.rb * d.normA * dist u v := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have : ∀ r ∈ range n, |(d.Aq k r : ℝ) * ∑ l ∈ range n, (d.J m r l - d.Jq r l) * w l| ≤
          |(d.Aq k r : ℝ)| * (16 * d.rb * dist u v) := by
        intro r hr
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (J_sub_bound hn hg hC hB m hmB w hwD (Finset.mem_range.mp hr))
          (abs_nonneg _)
      refine le_trans (Finset.sum_le_sum this) ?_
      rw [← Finset.sum_mul]
      have := hnA k hk
      have hD : 0 ≤ 16 * (d.rb : ℝ) * dist u v := by positivity
      nlinarith
    calc _ ≤ _ := abs_sub _ _
      _ ≤ d.q0 * dist u v + 16 * d.rb * d.normA * dist u v := add_le_add b1 b2
      _ = d.qq * dist u v := by rw [hqqR]; ring
  -- the box is mapped into itself
  have hTc : ∀ k : Fin n, |T c k - c k| ≤ d.normAF := by
    intro k
    have hEc : ∀ r < n, d.F (E c) r = (d.Fq r : ℝ) := by
      intro r hr
      have hEc' : ∀ l < n, E c l = (d.utq l : ℝ) := by intro l hl; simp [E, c, hl]
      have hl1 : ∀ l, l < 2 * d.N + 1 → E c l = (d.utq l : ℝ) := fun l hl => hEc' l (by omega)
      by_cases h1 : r < d.nC
      · obtain ⟨hi, hj⟩ := hC r h1
        simp only [F, Fq, if_pos h1]
        rw [hl1 _ (by omega), hl1 _ (by omega), hl1 _ (by omega), hl1 _ (by omega)]
        push_cast; ring
      · by_cases h2 : r < d.nC + d.nB
        · have hb := hB (r - d.nC) (by omega)
          simp only [F, Fq, if_neg h1, if_pos h2]
          rw [hl1 _ (by omega), hl1 _ (by omega), hl1 _ (by omega)]
          push_cast; ring
        · simp only [F, Fq, if_neg h1, if_neg h2]
          rw [hl1 _ (by omega)]
    have : T c k - c k = -∑ r ∈ range n, (d.Aq k r : ℝ) * (d.Fq r : ℝ) := by
      simp only [T]
      rw [Finset.sum_congr rfl (fun r hr => by rw [hEc r (Finset.mem_range.mp hr)])]
      ring
    rw [this, abs_neg]
    have h := le_foldl_max n (fun k => |∑ r ∈ range n, d.Aq k r * d.Fq r|) k.isLt
    have h' : ((|∑ r ∈ range n, d.Aq k r * d.Fq r| : ℚ) : ℝ) ≤ (d.normAF : ℝ) := by exact_mod_cast h
    push_cast at h'
    exact h'
  have hcs : c ∈ s := Metric.mem_closedBall_self hrbR.le
  have hmaps : Set.MapsTo T s s := by
    intro u hu
    rw [hmem]
    intro k
    have h1 := hlip u hu c hcs k
    have h2 := hTc k
    have hdu : dist u c ≤ d.rb := Metric.mem_closedBall.mp hu
    have hAFR : (d.normAF : ℝ) ≤ (1 - d.qq) * d.rb := by
      have := (Rat.cast_le (K := ℝ)).mpr hAF
      push_cast at this
      exact this
    have : |T u k - c k| ≤ |T u k - T c k| + |T c k - c k| := abs_sub_le _ _ _
    have h3 : (d.qq : ℝ) * dist u c ≤ d.qq * d.rb := mul_le_mul_of_nonneg_left hdu hqq0
    simp only [c] at this ⊢
    linarith
  -- Banach
  set K : NNReal := ⟨d.qq, hqq0⟩ with hK
  have hcontr : ContractingWith K (hmaps.restrict T s s) := by
    refine ⟨?_, ?_⟩
    · rw [← NNReal.coe_lt_coe]
      show (d.qq : ℝ) < ((1 : NNReal) : ℝ)
      simpa using hqq1
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Subtype.dist_eq, Subtype.dist_eq]
    simp only [Set.MapsTo.val_restrict_apply, hK, NNReal.coe_mk]
    rw [dist_pi_le_iff (by positivity)]
    intro k
    rw [Real.dist_eq]
    exact hlip x x.2 y y.2 k
  obtain ⟨y, hys, hfix, -⟩ := hcontr.exists_fixedPoint' (Metric.isClosed_closedBall.isComplete) hmaps hcs
    (edist_ne_top _ _)
  -- `A F(y) = 0`
  have hAF0 : ∀ k : Fin n, ∑ r ∈ range n, (d.Aq k r : ℝ) * d.F (E y) r = 0 := by
    intro k
    have := congrFun hfix k
    simp only [T] at this
    linarith
  -- `A` is injective: hence `F(y) = 0`
  set wv : ℕ → ℝ := fun r => d.F (E y) r with hwv
  obtain ⟨r0, hr0, hmax⟩ := Finset.exists_max_image (range n) (fun r => |wv r|) ⟨0, Finset.mem_range.mpr hn0⟩
  have hq1R : (d.q1 : ℝ) < 1 := by exact_mod_cast hq1
  have hrow : ∀ r < n, |wv r| ≤ d.q1 * |wv r0| := by
    intro r hr
    have hid : wv r = ∑ s ∈ range n, ((if r = s then (1 : ℝ) else 0) -
        ∑ k ∈ range n, (d.Jq r k : ℝ) * d.Aq k s) * wv s := by
      have hzero : ∑ k ∈ range n, (d.Jq r k : ℝ) * ∑ s ∈ range n, (d.Aq k s : ℝ) * wv s = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        have := hAF0 ⟨k, Finset.mem_range.mp hk⟩
        simp only at this
        rw [this, mul_zero]
      simp only [sub_mul, Finset.sum_sub_distrib]
      rw [Finset.sum_eq_single r]
      · simp only [ite_true, one_mul]
        have e : ∑ x ∈ range n, (∑ k ∈ range n, (d.Jq r k : ℝ) * d.Aq k x) * wv x =
            ∑ k ∈ range n, (d.Jq r k : ℝ) * ∑ s ∈ range n, (d.Aq k s : ℝ) * wv s := by
          simp only [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro k _
          apply Finset.sum_congr rfl; intro s _
          ring
        rw [e, hzero, sub_zero]
      · intro b _ hb; simp [Ne.symm hb]
      · intro h; exact absurd (Finset.mem_range.mpr hr) h
    rw [hid]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hrowq : (∑ s ∈ range n, |(if r = s then (1 : ℝ) else 0) - ∑ k ∈ range n, (d.Jq r k : ℝ) * d.Aq k s|) ≤
        d.q1 := by
      have h0 : (∑ s ∈ range n, |(if r = s then 1 else 0) - ∑ k ∈ range n, d.Jq r k * d.Aq k s| : ℚ) ≤ d.q1 :=
        le_foldl_max n (fun r => ∑ s ∈ range n, |(if r = s then 1 else 0) - ∑ k ∈ range n, d.Jq r k * d.Aq k s|) hr
      have h' : ((∑ s ∈ range n, |(if r = s then 1 else 0) - ∑ k ∈ range n, d.Jq r k * d.Aq k s| : ℚ) : ℝ) ≤
          (d.q1 : ℝ) := by exact_mod_cast h0
      push_cast at h'
      convert h' using 3
      split_ifs <;> simp
    calc ∑ s ∈ range n, |((if r = s then (1 : ℝ) else 0) - ∑ k ∈ range n, (d.Jq r k : ℝ) * d.Aq k s) * wv s|
        ≤ ∑ s ∈ range n, |(if r = s then (1 : ℝ) else 0) - ∑ k ∈ range n, (d.Jq r k : ℝ) * d.Aq k s| * |wv r0| := by
          apply Finset.sum_le_sum
          intro s hs
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hmax s hs) (abs_nonneg _)
      _ = (∑ s ∈ range n, |(if r = s then (1 : ℝ) else 0) - ∑ k ∈ range n, (d.Jq r k : ℝ) * d.Aq k s|) * |wv r0| := by
          rw [Finset.sum_mul]
      _ ≤ d.q1 * |wv r0| := mul_le_mul_of_nonneg_right hrowq (abs_nonneg _)
  have hw0 : |wv r0| = 0 := by
    have h := hrow r0 (Finset.mem_range.mp hr0)
    have hq1n : (0 : ℝ) ≤ d.q1 := by exact_mod_cast foldl_max_nonneg _ _
    nlinarith [abs_nonneg (wv r0)]
  refine ⟨E y, ?_, ?_⟩
  · intro k hk
    have := (hmem y).mp hys ⟨k, hk⟩
    simpa [E, hk] using this
  · intro r hr
    have h := hmax r (Finset.mem_range.mpr hr)
    rw [hw0] at h
    have : |wv r| = 0 := le_antisymm h (abs_nonneg _)
    simpa [hwv] using abs_eq_zero.mp this

end CirclePacking
