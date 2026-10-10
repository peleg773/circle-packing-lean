import CirclePacking.L7Data

/-!
# Local uniqueness of the record configuration (lemma L7)

`c*` (exact coordinates in `K = ℚ(sin π/5)`, see `L7Data`) is locally unique: every configuration `z`
(30 coordinates) satisfying the 20 contact constraints `|z_i - z_j|² ≥ 4`, the 10 boundary constraints
`|z_i|² ≤ ρ*²` and the gauge `z_1 = 0`, and lying within squared distance `R2` of `c*`, equals `c*`.
-/

open Real Finset

namespace CirclePacking

/-! ### Data access -/

def cst (i : ℕ) : QK × QK := cstarL.getD i default
def cx (i : ℕ) : QK := (cst i).1
def cy (i : ℕ) : QK := (cst i).2
/-- coordinate `c` of `c*` (`c = 2i`: x of point `i`; `c = 2i+1`: y of point `i`) -/
def cc (c : ℕ) : QK := if c % 2 = 0 then cx (c / 2) else cy (c / 2)
def ctc (r : ℕ) : ℕ × ℕ := contactsL.getD r (0, 0)
def bdi (t : ℕ) : ℕ := bndL.getD t 0
def mult (r : ℕ) : QK := multL.getD r default
def Mi (i r : ℕ) : QK := (MinvL.getD i []).getD r default
def fcol (i : ℕ) : ℕ := freeCols.getD i 0

/-- the linearised constraints -/
def Lm (r c : ℕ) : QK :=
  if r < 20 then
    (if c = 2 * (ctc r).1 then 2 * (cx (ctc r).1 - cx (ctc r).2) else 0) +
    (if c = 2 * (ctc r).1 + 1 then 2 * (cy (ctc r).1 - cy (ctc r).2) else 0) +
    (if c = 2 * (ctc r).2 then -(2 * (cx (ctc r).1 - cx (ctc r).2)) else 0) +
    (if c = 2 * (ctc r).2 + 1 then -(2 * (cy (ctc r).1 - cy (ctc r).2)) else 0)
  else
    (if c = 2 * bdi (r - 20) then -(2 * cx (bdi (r - 20))) else 0) +
    (if c = 2 * bdi (r - 20) + 1 then -(2 * cy (bdi (r - 20))) else 0)

def sumQ (n : ℕ) (f : ℕ → QK) : QK := (List.range n).foldl (fun acc r => acc + f r) 0

/-! ### Exact checks (kernel-decided) -/

def contactsOK : Bool := (List.range 20).all fun r =>
  let i := (ctc r).1; let j := (ctc r).2
  decide (i < 15) && decide (j < 15) && decide (i ≠ j) &&
  decide ((cx i - cx j) * (cx i - cx j) + (cy i - cy j) * (cy i - cy j) = 4)

def bndOK : Bool := (List.range 10).all fun t =>
  decide (bdi t < 15) && decide (cx (bdi t) * cx (bdi t) + cy (bdi t) * cy (bdi t) = rho2K)

def kktOK : Bool := (List.range 30).all fun c => decide (sumQ 30 (fun r => mult r * Lm r c) = 0)

def invOK : Bool := (List.range 29).all fun i => (List.range 29).all fun j =>
  decide (sumQ 30 (fun r => Mi i r * Lm r (fcol j)) = if i = j then 1 else 0)

def gaugeOK : Bool :=
  decide (cy 0 = 0) && (List.range 29).all (fun j => decide (fcol j = if j = 0 then 0 else j + 1))

/-! ### Certified constants -/

def qbar : ℚ := 7

/-- the bound `2 Σ_{contacts ∋ p} y_r ≤ qbar` -/
def weight (p : ℕ) : ℚ := (List.range 20).foldl (fun acc r =>
  acc + (if (ctc r).1 = p then QK.hi (mult r) else 0) + (if (ctc r).2 = p then QK.hi (mult r) else 0)) 0

def multPosOK : Bool := (List.range 30).all fun r => decide (0 < QK.lo (mult r))
def weightOK : Bool := (List.range 15).all fun p => decide (2 * weight p ≤ qbar)

def arow (r : ℕ) : ℚ := if r < 20 then max (qbar / QK.lo (mult r)) 2 else qbar / QK.lo (mult r) + 1
def K2 : ℚ := (List.range 30).foldl (fun acc r => acc + arow r ^ 2) 0
def MF2 : ℚ := (List.range 29).foldl (fun acc i =>
  (List.range 30).foldl (fun acc' r => acc' + QK.hi (Mi i r * Mi i r)) acc) 0
/-- squared radius of the uniqueness neighbourhood -/
def R2 : ℚ := 17 / 5000000
def boundOK : Bool := decide (R2 * MF2 * K2 < 1)

/-! ### Sums -/

lemma eval_sumQ (n : ℕ) (f : ℕ → QK) : (sumQ n f).eval = ∑ r ∈ range n, (f r).eval := by
  unfold sumQ
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.foldl_append, Finset.sum_range_succ, ← ih]; simp

lemma foldl_add_eq_sum (n : ℕ) (f : ℕ → ℚ) (a : ℚ) :
    (List.range n).foldl (fun acc r => acc + f r) a = a + ∑ r ∈ range n, f r := by
  induction n generalizing a with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.foldl_append, Finset.sum_range_succ, ih]; simp; ring

lemma sum_range_two_mul (m : ℕ) (f : ℕ → ℝ) :
    ∑ c ∈ range (2 * m), f c = ∑ p ∈ range m, (f (2 * p) + f (2 * p + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring

lemma QK.eval_ite (p : Prop) [Decidable p] (x : QK) :
    (if p then x else 0).eval = if p then x.eval else 0 := by
  split_ifs <;> simp

/-- `Σ_c (if c = a then x else 0) * δ c = x * δ a` for `a < n` -/
lemma sum_ite_mul {n a : ℕ} (ha : a < n) (x : ℝ) (δ : ℕ → ℝ) :
    ∑ c ∈ range n, (if c = a then x else 0) * δ c = x * δ a := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_range.mpr ha) h

/-! ### Extracting the exact checks -/

lemma contactsOK_spec (h : contactsOK = true) {r : ℕ} (hr : r < 20) :
    (ctc r).1 < 15 ∧ (ctc r).2 < 15 ∧ (ctc r).1 ≠ (ctc r).2 ∧
    (cx (ctc r).1 - cx (ctc r).2).eval ^ 2 + (cy (ctc r).1 - cy (ctc r).2).eval ^ 2 = 4 := by
  unfold contactsOK at h
  rw [List.all_eq_true] at h
  have h1 := h r (List.mem_range.mpr hr)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  obtain ⟨⟨⟨hi, hj⟩, hij⟩, he⟩ := h1
  refine ⟨hi, hj, hij, ?_⟩
  have := congrArg QK.eval he
  simp only [QK.eval_add, QK.eval_mul] at this
  rw [show (4 : QK).eval = 4 by show (QK.ofQ 4).eval = 4; simp] at this
  nlinarith [this]

lemma bndOK_spec (h : bndOK = true) {t : ℕ} (ht : t < 10) :
    bdi t < 15 ∧ (cx (bdi t)).eval ^ 2 + (cy (bdi t)).eval ^ 2 = rho2K.eval := by
  unfold bndOK at h
  rw [List.all_eq_true] at h
  have h1 := h t (List.mem_range.mpr ht)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  obtain ⟨hb, he⟩ := h1
  refine ⟨hb, ?_⟩
  have := congrArg QK.eval he
  simp only [QK.eval_add, QK.eval_mul] at this
  nlinarith [this]

lemma kktOK_spec (h : kktOK = true) {c : ℕ} (hc : c < 30) :
    ∑ r ∈ range 30, (mult r).eval * (Lm r c).eval = 0 := by
  unfold kktOK at h
  rw [List.all_eq_true] at h
  have h1 := h c (List.mem_range.mpr hc)
  simp only [decide_eq_true_eq] at h1
  have := congrArg QK.eval h1
  rw [eval_sumQ] at this
  simpa using this

lemma invOK_spec (h : invOK = true) {i j : ℕ} (hi : i < 29) (hj : j < 29) :
    ∑ r ∈ range 30, (Mi i r).eval * (Lm r (fcol j)).eval = if i = j then 1 else 0 := by
  unfold invOK at h
  rw [List.all_eq_true] at h
  have h1 := h i (List.mem_range.mpr hi)
  rw [List.all_eq_true] at h1
  have h2 := h1 j (List.mem_range.mpr hj)
  simp only [decide_eq_true_eq] at h2
  have := congrArg QK.eval h2
  rw [eval_sumQ] at this
  simp only [QK.eval_mul] at this
  rw [this]
  split_ifs <;> simp

lemma gaugeOK_spec (h : gaugeOK = true) :
    (cy 0).eval = 0 ∧ ∀ j < 29, fcol j = if j = 0 then 0 else j + 1 := by
  unfold gaugeOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨h0, h1⟩ := h
  exact ⟨by rw [h0]; simp, h1⟩

lemma multPos_spec (h : multPosOK = true) {r : ℕ} (hr : r < 30) :
    0 < QK.lo (mult r) ∧ ((QK.lo (mult r) : ℚ) : ℝ) ≤ (mult r).eval := by
  unfold multPosOK at h
  rw [List.all_eq_true] at h
  have h1 := h r (List.mem_range.mpr hr)
  simp only [decide_eq_true_eq] at h1
  exact ⟨h1, QK.lo_le_eval _⟩

lemma cc_even (p : ℕ) : cc (2 * p) = cx p := by simp [cc]
lemma cc_odd (p : ℕ) : cc (2 * p + 1) = cy p := by
  simp [cc, Nat.add_mod, show (2 * p + 1) / 2 = p by omega]

/-! ### The linearised constraints -/

lemma ell_contact (h : contactsOK = true) {r : ℕ} (hr : r < 20) (δ : ℕ → ℝ) :
    ∑ c ∈ range 30, (Lm r c).eval * δ c =
      2 * (cx (ctc r).1 - cx (ctc r).2).eval * (δ (2 * (ctc r).1) - δ (2 * (ctc r).2)) +
      2 * (cy (ctc r).1 - cy (ctc r).2).eval * (δ (2 * (ctc r).1 + 1) - δ (2 * (ctc r).2 + 1)) := by
  obtain ⟨hi, hj, -, -⟩ := contactsOK_spec h hr
  have e : ∀ c, (Lm r c).eval * δ c =
      (if c = 2 * (ctc r).1 then (2 * (cx (ctc r).1 - cx (ctc r).2)).eval else 0) * δ c +
      (if c = 2 * (ctc r).1 + 1 then (2 * (cy (ctc r).1 - cy (ctc r).2)).eval else 0) * δ c +
      (if c = 2 * (ctc r).2 then (-(2 * (cx (ctc r).1 - cx (ctc r).2))).eval else 0) * δ c +
      (if c = 2 * (ctc r).2 + 1 then (-(2 * (cy (ctc r).1 - cy (ctc r).2))).eval else 0) * δ c := by
    intro c
    simp only [Lm, if_pos hr, QK.eval_add, QK.eval_ite]
    ring
  simp only [e, Finset.sum_add_distrib]
  rw [sum_ite_mul (by omega), sum_ite_mul (by omega), sum_ite_mul (by omega), sum_ite_mul (by omega)]
  simp only [QK.eval_neg, QK.eval_mul, QK.eval_sub]
  rw [show (2 : QK).eval = 2 by show (QK.ofQ 2).eval = 2; simp]
  ring

lemma ell_bnd (h : bndOK = true) {r : ℕ} (hr1 : 20 ≤ r) (hr2 : r < 30) (δ : ℕ → ℝ) :
    ∑ c ∈ range 30, (Lm r c).eval * δ c =
      -2 * (cx (bdi (r - 20))).eval * δ (2 * bdi (r - 20)) -
      2 * (cy (bdi (r - 20))).eval * δ (2 * bdi (r - 20) + 1) := by
  obtain ⟨hb, -⟩ := bndOK_spec h (show r - 20 < 10 by omega)
  have e : ∀ c, (Lm r c).eval * δ c =
      (if c = 2 * bdi (r - 20) then (-(2 * cx (bdi (r - 20)))).eval else 0) * δ c +
      (if c = 2 * bdi (r - 20) + 1 then (-(2 * cy (bdi (r - 20)))).eval else 0) * δ c := by
    intro c
    simp only [Lm, if_neg (show ¬ r < 20 by omega), QK.eval_add, QK.eval_ite]
    ring
  simp only [e, Finset.sum_add_distrib]
  rw [sum_ite_mul (by omega), sum_ite_mul (by omega)]
  simp only [QK.eval_neg, QK.eval_mul]
  rw [show (2 : QK).eval = 2 by show (QK.ofQ 2).eval = 2; simp]
  ring

/-! ### Auxiliary inequalities -/

lemma weight_eq (p : ℕ) : weight p = ∑ r ∈ range 20,
    ((if (ctc r).1 = p then QK.hi (mult r) else 0) + (if (ctc r).2 = p then QK.hi (mult r) else 0)) := by
  unfold weight
  have := foldl_add_eq_sum 20 (fun r =>
    (if (ctc r).1 = p then QK.hi (mult r) else 0) + (if (ctc r).2 = p then QK.hi (mult r) else 0)) 0
  simp only [zero_add] at this
  rw [← this]
  congr 1
  ext acc r
  ring

/-- regrouping a sum over contacts into a sum over points -/
lemma sum_contacts_points (hC : contactsOK = true) (w : ℕ → ℝ) (P : ℕ → ℝ) :
    ∑ r ∈ range 20, w r * (P (ctc r).1 + P (ctc r).2) =
      ∑ p ∈ range 15, P p * ∑ r ∈ range 20,
        ((if (ctc r).1 = p then w r else 0) + (if (ctc r).2 = p then w r else 0)) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  obtain ⟨hi, hj, -, -⟩ := contactsOK_spec hC (Finset.mem_range.mp hr)
  rw [mul_add, Finset.sum_congr rfl (fun p _ => by rw [mul_add])]
  rw [Finset.sum_add_distrib]
  have e1 : ∑ p ∈ range 15, P p * (if (ctc r).1 = p then w r else 0) = w r * P (ctc r).1 := by
    rw [Finset.sum_eq_single (ctc r).1]
    · simp; ring
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_range.mpr hi) h
  have e2 : ∑ p ∈ range 15, P p * (if (ctc r).2 = p then w r else 0) = w r * P (ctc r).2 := by
    rw [Finset.sum_eq_single (ctc r).2]
    · simp; ring
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_range.mpr hj) h
  rw [e1, e2]

/-- Cauchy–Schwarz for finite sums -/
lemma sq_sum_le (n : ℕ) (a b : ℕ → ℝ) :
    (∑ r ∈ range n, a r * b r) ^ 2 ≤ (∑ r ∈ range n, a r ^ 2) * (∑ r ∈ range n, b r ^ 2) :=
  Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-! ### The local uniqueness theorem -/

theorem local_unique (hC : contactsOK = true) (hB : bndOK = true) (hK : kktOK = true)
    (hI : invOK = true) (hG : gaugeOK = true) (hM : multPosOK = true) (hW : weightOK = true)
    (hR : boundOK = true) (z : ℕ → ℝ)
    (hc : ∀ r < 20, 4 ≤ (z (2 * (ctc r).1) - z (2 * (ctc r).2)) ^ 2 +
        (z (2 * (ctc r).1 + 1) - z (2 * (ctc r).2 + 1)) ^ 2)
    (hb : ∀ t < 10, z (2 * bdi t) ^ 2 + z (2 * bdi t + 1) ^ 2 ≤ rho2K.eval)
    (hg : z 1 = 0)
    (hclose : ∑ c ∈ range 30, (z c - (cc c).eval) ^ 2 < R2) :
    ∀ c < 30, z c = (cc c).eval := by
  classical
  set δ : ℕ → ℝ := fun c => z c - (cc c).eval with hδdef
  set nd : ℝ := ∑ c ∈ range 30, δ c ^ 2 with hnd
  have hnd0 : 0 ≤ nd := Finset.sum_nonneg (fun c _ => sq_nonneg _)
  set Pn : ℕ → ℝ := fun p => δ (2 * p) ^ 2 + δ (2 * p + 1) ^ 2 with hPn
  have hPn0 : ∀ p, 0 ≤ Pn p := fun p => by simp only [hPn]; positivity
  have hnd_pts : nd = ∑ p ∈ range 15, Pn p := by
    rw [hnd, show (30 : ℕ) = 2 * 15 by norm_num, sum_range_two_mul]
  have hPn_le : ∀ p < 15, Pn p ≤ nd := by
    intro p hp
    rw [hnd_pts]
    exact Finset.single_le_sum (fun q _ => hPn0 q) (Finset.mem_range.mpr hp)
  have hPn_pair : ∀ p q, p < 15 → q < 15 → p ≠ q → Pn p + Pn q ≤ nd := by
    intro p q hp hq hpq
    rw [hnd_pts]
    have hsub : ({p, q} : Finset ℕ) ⊆ range 15 := by
      intro x hx; simp at hx; rcases hx with rfl | rfl <;> simp [hp, hq]
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hPn0 x)
    rwa [Finset.sum_pair hpq] at this
  have hzx : ∀ p, z (2 * p) = (cx p).eval + δ (2 * p) := by
    intro p; simp only [hδdef, cc_even]; ring
  have hzy : ∀ p, z (2 * p + 1) = (cy p).eval + δ (2 * p + 1) := by
    intro p; simp only [hδdef, cc_odd]; ring
  -- linear parts and constraint values
  set ℓ : ℕ → ℝ := fun r => ∑ c ∈ range 30, (Lm r c).eval * δ c with hℓ
  set g : ℕ → ℝ := fun r => if r < 20 then
      (z (2 * (ctc r).1) - z (2 * (ctc r).2)) ^ 2 + (z (2 * (ctc r).1 + 1) - z (2 * (ctc r).2 + 1)) ^ 2 - 4
    else rho2K.eval - (z (2 * bdi (r - 20)) ^ 2 + z (2 * bdi (r - 20) + 1) ^ 2) with hgdef
  set qd : ℕ → ℝ := fun r => if r < 20 then
      (δ (2 * (ctc r).1) - δ (2 * (ctc r).2)) ^ 2 + (δ (2 * (ctc r).1 + 1) - δ (2 * (ctc r).2 + 1)) ^ 2
    else -Pn (bdi (r - 20)) with hqd
  have hgq : ∀ r < 30, g r = ℓ r + qd r := by
    intro r hr
    by_cases h20 : r < 20
    · obtain ⟨hi, hj, hij, h4⟩ := contactsOK_spec hC h20
      simp only [hgdef, hqd, hℓ, if_pos h20]
      rw [ell_contact hC h20, hzx, hzx, hzy, hzy]
      simp only [QK.eval_sub] at h4 ⊢
      linear_combination h4
    · obtain ⟨hb15, hr2⟩ := bndOK_spec hB (show r - 20 < 10 by omega)
      simp only [hgdef, hqd, hℓ, if_neg h20]
      rw [ell_bnd hB (by omega) hr, hzx, hzy]
      simp only [hPn]
      linear_combination -hr2
  have hg0 : ∀ r < 30, 0 ≤ g r := by
    intro r hr
    by_cases h20 : r < 20
    · simp only [hgdef, if_pos h20]; linarith [hc r h20]
    · simp only [hgdef, if_neg h20]; linarith [hb (r - 20) (by omega)]
  -- multipliers
  set y : ℕ → ℝ := fun r => (mult r).eval with hy
  have hylo : ∀ r < 30, 0 < QK.lo (mult r) ∧ ((QK.lo (mult r) : ℚ) : ℝ) ≤ y r :=
    fun r hr => multPos_spec hM hr
  have hy0 : ∀ r < 30, 0 < y r := by
    intro r hr
    obtain ⟨h1, h2⟩ := hylo r hr
    exact lt_of_lt_of_le (by exact_mod_cast h1) h2
  -- KKT identity
  have hkkt : ∑ r ∈ range 30, y r * ℓ r = 0 := by
    simp only [hy, hℓ, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro c hc
    have := kktOK_spec hK (Finset.mem_range.mp hc)
    calc ∑ x ∈ range 30, (mult x).eval * ((Lm x c).eval * δ c)
        = (∑ x ∈ range 30, (mult x).eval * (Lm x c).eval) * δ c := by
          rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro x _; ring
      _ = 0 := by rw [this]; ring
  have hyg : ∑ r ∈ range 30, y r * g r = ∑ r ∈ range 30, y r * qd r := by
    rw [show ∑ r ∈ range 30, y r * g r = ∑ r ∈ range 30, (y r * ℓ r + y r * qd r) from
      Finset.sum_congr rfl (fun r hr => by rw [hgq r (Finset.mem_range.mp hr)]; ring)]
    rw [Finset.sum_add_distrib, hkkt, zero_add]
  -- the weighted quadratic part is at most `qbar * nd`
  have hqd_contact : ∀ r < 20, qd r ≤ 2 * (Pn (ctc r).1 + Pn (ctc r).2) := by
    intro r hr
    simp only [hqd, if_pos hr, hPn]
    nlinarith [sq_nonneg (δ (2 * (ctc r).1) + δ (2 * (ctc r).2)),
      sq_nonneg (δ (2 * (ctc r).1 + 1) + δ (2 * (ctc r).2 + 1))]
  have hyq : ∑ r ∈ range 30, y r * qd r ≤ qbar * nd := by
    have hsplit : ∑ r ∈ range 30, y r * qd r =
        ∑ r ∈ range 20, y r * qd r + ∑ r ∈ Finset.Ico 20 30, y r * qd r := by
      rw [← Finset.sum_range_add_sum_Ico _ (by norm_num : 20 ≤ 30)]
    have hneg : ∑ r ∈ Finset.Ico 20 30, y r * qd r ≤ 0 := by
      apply Finset.sum_nonpos
      intro r hr
      rw [Finset.mem_Ico] at hr
      simp only [hqd, if_neg (show ¬ r < 20 by omega)]
      have := hy0 r (by omega)
      have := hPn0 (bdi (r - 20))
      nlinarith
    have hcont : ∑ r ∈ range 20, y r * qd r ≤ ∑ r ∈ range 20, (2 * y r) * (Pn (ctc r).1 + Pn (ctc r).2) := by
      apply Finset.sum_le_sum
      intro r hr
      have hr' := Finset.mem_range.mp hr
      have := hqd_contact r hr'
      have := hy0 r (by omega)
      nlinarith
    rw [sum_contacts_points hC] at hcont
    have hw : ∀ p ∈ range 15, Pn p * ∑ r ∈ range 20,
        ((if (ctc r).1 = p then 2 * y r else 0) + (if (ctc r).2 = p then 2 * y r else 0)) ≤ Pn p * qbar := by
      intro p hp
      apply mul_le_mul_of_nonneg_left _ (hPn0 p)
      have hwp : 2 * weight p ≤ qbar := by
        unfold weightOK at hW
        rw [List.all_eq_true] at hW
        have := hW p (List.mem_range.mpr (Finset.mem_range.mp hp))
        simpa using this
      have hwR : ((2 * weight p : ℚ) : ℝ) ≤ (qbar : ℝ) := by exact_mod_cast hwp
      rw [weight_eq] at hwR
      push_cast at hwR
      refine le_trans ?_ hwR
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro r hr
      have hr' := Finset.mem_range.mp hr
      have hyhi : y r ≤ ((QK.hi (mult r) : ℚ) : ℝ) := QK.eval_le_hi _
      split_ifs <;> (try simp only [Rat.cast_zero] at *) <;> linarith
    have := Finset.sum_le_sum hw
    rw [← Finset.sum_mul, ← hnd_pts] at this
    linarith
  -- each constraint value is small
  have hgsmall : ∀ r < 30, g r ≤ (qbar : ℝ) / ((QK.lo (mult r) : ℚ) : ℝ) * nd := by
    intro r hr
    have hsingle : y r * g r ≤ ∑ r' ∈ range 30, y r' * g r' :=
      Finset.single_le_sum (fun r' hr' => mul_nonneg (hy0 r' (Finset.mem_range.mp hr')).le
        (hg0 r' (Finset.mem_range.mp hr'))) (Finset.mem_range.mpr hr)
    rw [hyg] at hsingle
    obtain ⟨hlo0, hlo⟩ := hylo r hr
    have hlo0' : (0 : ℝ) < ((QK.lo (mult r) : ℚ) : ℝ) := by exact_mod_cast hlo0
    have h1 : ((QK.lo (mult r) : ℚ) : ℝ) * g r ≤ qbar * nd := by
      have := mul_le_mul_of_nonneg_right hlo (hg0 r hr)
      linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hlo0']
    linarith
  -- the linear parts are small
  have hℓsmall : ∀ r < 30, |ℓ r| ≤ (arow r : ℝ) * nd := by
    intro r hr
    have hgs := hgsmall r hr
    have hgq' := hgq r hr
    have hg0' := hg0 r hr
    by_cases h20 : r < 20
    · obtain ⟨hi, hj, hij, -⟩ := contactsOK_spec hC h20
      have hq0 : 0 ≤ qd r := by simp only [hqd, if_pos h20]; positivity
      have hq2 : qd r ≤ 2 * nd := le_trans (hqd_contact r h20) (by linarith [hPn_pair _ _ hi hj hij])
      have ha : ((arow r : ℚ) : ℝ) = max ((qbar : ℝ) / ((QK.lo (mult r) : ℚ) : ℝ)) 2 := by
        simp only [arow, if_pos h20]; push_cast; rfl
      rw [ha, abs_le]
      constructor
      · have := le_max_right ((qbar : ℝ) / ((QK.lo (mult r) : ℚ) : ℝ)) 2
        nlinarith
      · have := le_max_left ((qbar : ℝ) / ((QK.lo (mult r) : ℚ) : ℝ)) 2
        nlinarith
    · obtain ⟨hb15, -⟩ := bndOK_spec hB (show r - 20 < 10 by omega)
      have hq : qd r = -Pn (bdi (r - 20)) := by simp only [hqd, if_neg h20]
      have hPb := hPn_le _ hb15
      have ha : ((arow r : ℚ) : ℝ) = (qbar : ℝ) / ((QK.lo (mult r) : ℚ) : ℝ) + 1 := by
        simp only [arow, if_neg h20]; push_cast; rfl
      rw [ha, abs_le]
      constructor <;> nlinarith [hPn0 (bdi (r - 20))]
  have hK2 : (K2 : ℝ) = ∑ r ∈ range 30, ((arow r : ℚ) : ℝ) ^ 2 := by
    have := foldl_add_eq_sum 30 (fun r => arow r ^ 2) 0
    simp only [zero_add] at this
    unfold K2; rw [this]; push_cast; rfl
  have hK0 : (0 : ℝ) ≤ (K2 : ℝ) := by rw [hK2]; exact Finset.sum_nonneg (fun r _ => sq_nonneg _)
  have hsumℓ : ∑ r ∈ range 30, ℓ r ^ 2 ≤ (K2 : ℝ) * nd ^ 2 := by
    rw [hK2, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro r hr
    have h := hℓsmall r (Finset.mem_range.mp hr)
    have h' : ℓ r ^ 2 ≤ ((arow r : ℝ) * nd) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
    nlinarith [h']
  -- inverse: δ on the free coordinates
  obtain ⟨hcy0, hfcol⟩ := gaugeOK_spec hG
  have hδ1 : δ 1 = 0 := by
    simp only [hδdef, hg]
    have : cc 1 = cy 0 := by simp [cc]
    rw [this, hcy0]; ring
  have hδfree : ∀ i < 29, δ (fcol i) = ∑ r ∈ range 30, (Mi i r).eval * ℓ r := by
    intro i hi
    simp only [hℓ, Finset.mul_sum]
    rw [Finset.sum_comm]
    -- split the coordinate sum into c = 1 and the free coordinates
    have hcoord : ∀ c ∈ range 30, ∑ r ∈ range 30, (Mi i r).eval * ((Lm r c).eval * δ c) =
        (∑ r ∈ range 30, (Mi i r).eval * (Lm r c).eval) * δ c := by
      intro c _; rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro r _; ring
    rw [Finset.sum_congr rfl hcoord]
    -- c ↦ coefficient: free coordinates give the Kronecker delta, c = 1 has δ 1 = 0
    have hval : ∀ c ∈ range 30, (∑ r ∈ range 30, (Mi i r).eval * (Lm r c).eval) * δ c =
        if c = fcol i then δ c else 0 := by
      intro c hc
      have hc' := Finset.mem_range.mp hc
      by_cases h1 : c = 1
      · subst h1
        rw [hδ1, mul_zero]
        split_ifs with h
        · rfl
        · rfl
      · -- c = fcol j for j = (c = 0 ? 0 : c - 1)
        have hj : ∃ j < 29, fcol j = c := by
          by_cases h0 : c = 0
          · exact ⟨0, by norm_num, by rw [hfcol 0 (by norm_num)]; simp [h0]⟩
          · refine ⟨c - 1, by omega, ?_⟩
            rw [hfcol (c - 1) (by omega)]
            simp only [show c - 1 ≠ 0 by omega, if_false]; omega
        obtain ⟨j, hj29, rfl⟩ := hj
        rw [invOK_spec hI hi hj29]
        by_cases hij : i = j
        · subst hij; simp
        · have hne : fcol j ≠ fcol i := by
            rw [hfcol j hj29, hfcol i hi]
            split_ifs <;> omega
          simp [hij, hne]
    rw [Finset.sum_congr rfl hval, Finset.sum_ite_eq']
    have : fcol i ∈ range 30 := by
      rw [Finset.mem_range, hfcol i hi]; split_ifs <;> omega
    simp [this]
  have hnd_free : nd = ∑ i ∈ range 29, δ (fcol i) ^ 2 := by
    rw [hnd]
    -- range 30 = {0} ∪ {1} ∪ {2..29}; reindex via fcol
    have h30 : ∑ c ∈ range 30, δ c ^ 2 = δ 0 ^ 2 + δ 1 ^ 2 + ∑ j ∈ range 28, δ (j + 2) ^ 2 := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      ring_nf
    have h29 : ∑ i ∈ range 29, δ (fcol i) ^ 2 = δ 0 ^ 2 + ∑ j ∈ range 28, δ (j + 2) ^ 2 := by
      rw [Finset.sum_range_succ']
      have e0 : fcol 0 = 0 := by rw [hfcol 0 (by norm_num)]; simp
      rw [e0, add_comm]
      have hs : ∑ j ∈ range 28, δ (fcol (j + 1)) ^ 2 = ∑ j ∈ range 28, δ (j + 2) ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hfcol (j + 1) (by have := Finset.mem_range.mp hj; omega)]
        simp
      rw [hs]
    rw [h30, h29, hδ1]; ring
  have hMF2 : (MF2 : ℝ) ≥ ∑ i ∈ range 29, ∑ r ∈ range 30, (Mi i r).eval ^ 2 := by
    have e1 : MF2 = ∑ i ∈ range 29, ∑ r ∈ range 30, QK.hi (Mi i r * Mi i r) := by
      unfold MF2
      have h := foldl_add_eq_sum 29 (fun i => ∑ r ∈ range 30, QK.hi (Mi i r * Mi i r)) 0
      simp only [zero_add] at h
      rw [← h]
      congr 1
      ext acc i
      have := foldl_add_eq_sum 30 (fun r => QK.hi (Mi i r * Mi i r)) acc
      rw [this]
    rw [e1]; push_cast
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro r _
    have := QK.eval_le_hi (Mi i r * Mi i r)
    rw [QK.eval_mul] at this
    nlinarith
  have hCS : nd ≤ (MF2 : ℝ) * (K2 : ℝ) * nd ^ 2 := by
    calc nd = ∑ i ∈ range 29, δ (fcol i) ^ 2 := hnd_free
      _ = ∑ i ∈ range 29, (∑ r ∈ range 30, (Mi i r).eval * ℓ r) ^ 2 :=
          Finset.sum_congr rfl (fun i hi => by rw [hδfree i (Finset.mem_range.mp hi)])
      _ ≤ ∑ i ∈ range 29, (∑ r ∈ range 30, (Mi i r).eval ^ 2) * (∑ r ∈ range 30, ℓ r ^ 2) :=
          Finset.sum_le_sum (fun i _ => sq_sum_le 30 _ _)
      _ = (∑ i ∈ range 29, ∑ r ∈ range 30, (Mi i r).eval ^ 2) * (∑ r ∈ range 30, ℓ r ^ 2) := by
          rw [Finset.sum_mul]
      _ ≤ (MF2 : ℝ) * ((K2 : ℝ) * nd ^ 2) := by
          apply mul_le_mul hMF2 hsumℓ (Finset.sum_nonneg (fun r _ => sq_nonneg _))
          exact le_trans (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun r _ => sq_nonneg _))) hMF2
      _ = (MF2 : ℝ) * (K2 : ℝ) * nd ^ 2 := by ring
  -- conclusion
  have hRb : (R2 : ℝ) * MF2 * K2 < 1 := by
    unfold boundOK at hR; simp only [decide_eq_true_eq] at hR; exact_mod_cast hR
  have hMK0 : (0 : ℝ) ≤ (MF2 : ℝ) * K2 := by
    have : (0 : ℝ) ≤ (MF2 : ℝ) := le_trans (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
      (fun r _ => sq_nonneg _))) hMF2
    positivity
  have hnd_zero : nd = 0 := by
    by_contra hne
    have hpos : 0 < nd := lt_of_le_of_ne hnd0 (Ne.symm hne)
    have h1 : 1 ≤ (MF2 : ℝ) * K2 * nd := by
      have := hCS
      rw [show (MF2 : ℝ) * K2 * nd ^ 2 = ((MF2 : ℝ) * K2 * nd) * nd by ring] at this
      exact (le_mul_iff_one_le_left hpos).mp (by linarith)
    have h2 : (MF2 : ℝ) * K2 * nd ≤ (MF2 : ℝ) * K2 * R2 :=
      mul_le_mul_of_nonneg_left hclose.le hMK0
    linarith
  intro c hc
  have hδc : δ c ^ 2 = 0 := by
    have := Finset.single_le_sum (fun c' _ => sq_nonneg (δ c')) (Finset.mem_range.mpr hc)
    rw [← hnd, hnd_zero] at this
    linarith [sq_nonneg (δ c)]
  have : δ c = 0 := by simpa using hδc
  simp only [hδdef] at this
  linarith

end CirclePacking
