import Mathlib

/-!
# Local uniqueness from approximate data (generic)

Let `c*` be a configuration of `N` points (coordinates `2p`, `2p+1`) satisfying contact equations
`|c*_i - c*_j|² = 4` for the pairs in `ctc`, boundary equations `|c*_b|² = P` for the points in `bnd`, and
a gauge equation `c*_g = 0`.  We only know `c*` up to `rb` in every coordinate: `|c*_c - c̃_c| ≤ rb` for an
explicit rational configuration `c̃`.  Given a positive stress `y` (approximately `yᵀ L̃ = 0`) and an
approximate left inverse `M` of the gauge-fixed linearisation `L̃` at `c̃`, all with *rational* entries,
the checks below (exact rational arithmetic, decided by the kernel) imply:

**every `z` with `|z_i - z_j|² ≥ 4` (contacts), `|z_b|² ≤ P` (boundary), `z_g = 0` and
`∑ (z - c*)² < R2` equals `c*`.**

The proof is the argument of `L7.lean` with explicit error terms: the stress residual `ε = yᵀL̃`, the
inverse residual `E = M L̃_free - I`, and the distance between the linearisations at `c*` and at `c̃`.
-/

open Finset

namespace CirclePacking

/-- data of a local uniqueness certificate -/
structure LUData where
  /-- number of points -/
  N : ℕ
  /-- contact pairs -/
  ctc : List (ℕ × ℕ)
  /-- boundary points -/
  bnd : List ℕ
  /-- the approximate configuration `c̃` (coordinates `2p`, `2p+1` of point `p`) -/
  ct : List ℚ
  /-- the stress (one weight per row: contacts first, then boundary points) -/
  y : List ℚ
  /-- the approximate left inverse (one row per free coordinate, one column per constraint row) -/
  M : List (List ℚ)
  /-- the gauge coordinate -/
  gauge : ℕ
  /-- coordinatewise distance bound between `c*` and `c̃` -/
  rb : ℚ
  /-- bound for the stress weight at a point -/
  qbar : ℚ
  /-- squared radius of the uniqueness neighbourhood -/
  R2 : ℚ

namespace LUData

variable (d : LUData)

def nC : ℕ := d.ctc.length
def nB : ℕ := d.bnd.length
/-- number of constraint rows -/
def nR : ℕ := d.nC + d.nB
/-- number of free coordinates (all but the gauge coordinate) -/
def nF : ℕ := 2 * d.N - 1

def ci (r : ℕ) : ℕ := (d.ctc.getD r (0, 0)).1
def cj (r : ℕ) : ℕ := (d.ctc.getD r (0, 0)).2
def bi (t : ℕ) : ℕ := d.bnd.getD t 0
def ctq (c : ℕ) : ℚ := d.ct.getD c 0
def yq (r : ℕ) : ℚ := d.y.getD r 0
def Mq (i r : ℕ) : ℚ := (d.M.getD i []).getD r 0
/-- the `i`-th free coordinate (the coordinates in increasing order, skipping the gauge coordinate) -/
def fcol (i : ℕ) : ℕ := if i < d.gauge then i else i + 1

/-- the linearisation at `c̃`: row `r`, coordinate `c` -/
def Lt (r c : ℕ) : ℚ :=
  if r < d.nC then
    (if c = 2 * d.ci r then 2 * (d.ctq (2 * d.ci r) - d.ctq (2 * d.cj r)) else 0) +
    (if c = 2 * d.ci r + 1 then 2 * (d.ctq (2 * d.ci r + 1) - d.ctq (2 * d.cj r + 1)) else 0) +
    (if c = 2 * d.cj r then -(2 * (d.ctq (2 * d.ci r) - d.ctq (2 * d.cj r))) else 0) +
    (if c = 2 * d.cj r + 1 then -(2 * (d.ctq (2 * d.ci r + 1) - d.ctq (2 * d.cj r + 1))) else 0)
  else
    (if c = 2 * d.bi (r - d.nC) then -(2 * d.ctq (2 * d.bi (r - d.nC))) else 0) +
    (if c = 2 * d.bi (r - d.nC) + 1 then -(2 * d.ctq (2 * d.bi (r - d.nC) + 1)) else 0)

/-- the stress residual `ε_c = ∑_r y_r L̃_{rc}` -/
def eps (c : ℕ) : ℚ := ∑ r ∈ range d.nR, d.yq r * d.Lt r c
/-- bound for `|∑_r y_r ℓ*_r| / |δ|` -/
def eta : ℚ := ∑ c ∈ range (2 * d.N), |d.eps c| + 16 * d.rb * ∑ r ∈ range d.nR, d.yq r
/-- the inverse residual `E = M L̃_free - I` -/
def Eq (i j : ℕ) : ℚ := ∑ r ∈ range d.nR, d.Mq i r * d.Lt r (d.fcol j) - if i = j then 1 else 0
def EF2 : ℚ := ∑ i ∈ range d.nF, ∑ j ∈ range d.nF, d.Eq i j ^ 2
def MF2 : ℚ := ∑ i ∈ range d.nF, ∑ r ∈ range d.nR, d.Mq i r ^ 2
/-- the coefficient of `|δ|²` in the bound for `|ℓ*_r|` -/
def arow (r : ℕ) : ℚ := if r < d.nC then max 2 (d.qbar / d.yq r) else d.qbar / d.yq r + 1
def K2 : ℚ := ∑ r ∈ range d.nR, d.arow r ^ 2
def H2 : ℚ := ∑ r ∈ range d.nR, (d.eta / d.yq r) ^ 2
/-- the total relative error -/
def tau : ℚ := 6 * d.MF2 * d.H2 + 768 * d.MF2 * d.nR * d.rb ^ 2 + 3 * d.EF2
/-- the stress weight at point `p` -/
def wt (p : ℕ) : ℚ := ∑ r ∈ range d.nC, ((if d.ci r = p then d.yq r else 0) + (if d.cj r = p then d.yq r else 0))

/-- all checks -/
def ok : Bool :=
  decide (0 < d.N) && decide (d.gauge < 2 * d.N) && decide (d.ct.length = 2 * d.N) &&
  (List.range d.nC).all (fun r => decide (d.ci r < d.N) && decide (d.cj r < d.N) && decide (d.ci r ≠ d.cj r)) &&
  (List.range d.nB).all (fun t => decide (d.bi t < d.N)) &&
  (List.range d.nR).all (fun r => decide (0 < d.yq r)) &&
  (List.range d.N).all (fun p => decide (2 * d.wt p ≤ d.qbar)) &&
  decide (0 ≤ d.rb) && decide (0 ≤ d.R2) &&
  decide (d.tau ≤ 1 / 2) && decide (12 * d.R2 * d.MF2 * d.K2 ≤ 1)

end LUData


namespace LUData

variable {d : LUData}

/-! ### Reading the checks -/

lemma ok_spec (h : d.ok = true) :
    0 < d.N ∧ d.gauge < 2 * d.N ∧ d.ct.length = 2 * d.N ∧
    (∀ r < d.nC, d.ci r < d.N ∧ d.cj r < d.N ∧ d.ci r ≠ d.cj r) ∧
    (∀ t < d.nB, d.bi t < d.N) ∧ (∀ r < d.nR, 0 < d.yq r) ∧
    (∀ p < d.N, 2 * d.wt p ≤ d.qbar) ∧ 0 ≤ d.rb ∧ 0 ≤ d.R2 ∧ d.tau ≤ 1 / 2 ∧
    12 * d.R2 * d.MF2 * d.K2 ≤ 1 := by
  unfold ok at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  refine ⟨h1, h2, h3, fun r hr => ?_, h5, h6, h7, h8, h9, h10, h11⟩
  have := h4 r hr
  simp only [ne_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

end LUData

/-! ### Sums over coordinates -/

lemma sum_free {N g : ℕ} (hg : g < 2 * N) (h : ℕ → ℝ) :
    ∑ c ∈ range (2 * N), h c = h g + ∑ i ∈ range (2 * N - 1), h (if i < g then i else i + 1) := by
  have e1 : ∑ c ∈ range (2 * N), h c = ∑ c ∈ range g, h c + ∑ c ∈ Ico g (2 * N), h c :=
    (Finset.sum_range_add_sum_Ico _ hg.le).symm
  have e2 : ∑ c ∈ Ico g (2 * N), h c = h g + ∑ c ∈ Ico (g + 1) (2 * N), h c :=
    Finset.sum_eq_sum_Ico_succ_bot hg _
  have e3 : ∑ i ∈ range (2 * N - 1), h (if i < g then i else i + 1) =
      ∑ i ∈ range g, h (if i < g then i else i + 1) +
        ∑ i ∈ Ico g (2 * N - 1), h (if i < g then i else i + 1) :=
    (Finset.sum_range_add_sum_Ico _ (by omega)).symm
  have e4 : ∑ i ∈ range g, h (if i < g then i else i + 1) = ∑ i ∈ range g, h i :=
    Finset.sum_congr rfl (fun i hi => by rw [if_pos (Finset.mem_range.mp hi)])
  have e5 : ∑ i ∈ Ico g (2 * N - 1), h (if i < g then i else i + 1) = ∑ i ∈ Ico g (2 * N - 1), h (i + 1) :=
    Finset.sum_congr rfl (fun i hi => by rw [if_neg (by rw [Finset.mem_Ico] at hi; omega)])
  have e6 : ∑ i ∈ Ico g (2 * N - 1), h (i + 1) = ∑ c ∈ Ico (g + 1) (2 * N), h c := by
    rw [Finset.sum_Ico_add']
    congr 2
    omega
  rw [e1, e2, e3, e4, e5, e6]
  ring

lemma sum_two_mul (m : ℕ) (f : ℕ → ℝ) :
    ∑ c ∈ range (2 * m), f c = ∑ p ∈ range m, (f (2 * p) + f (2 * p + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring

lemma sum_ite_eq_mul {n a : ℕ} (ha : a < n) (x : ℝ) (δ : ℕ → ℝ) :
    ∑ c ∈ range n, (if c = a then x else 0) * δ c = x * δ a := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_range.mpr ha) h

namespace LUData

variable {d : LUData}

/-- real-valued data -/
noncomputable def ctR (c : ℕ) : ℝ := (d.ctq c : ℝ)

lemma Lt_contact {r : ℕ} (hr : r < d.nC) (hij : d.ci r < d.N ∧ d.cj r < d.N ∧ d.ci r ≠ d.cj r)
    (δ : ℕ → ℝ) :
    ∑ c ∈ range (2 * d.N), (d.Lt r c : ℝ) * δ c =
      2 * ((d.ctq (2 * d.ci r) : ℝ) - d.ctq (2 * d.cj r)) * (δ (2 * d.ci r) - δ (2 * d.cj r)) +
      2 * ((d.ctq (2 * d.ci r + 1) : ℝ) - d.ctq (2 * d.cj r + 1)) * (δ (2 * d.ci r + 1) - δ (2 * d.cj r + 1)) := by
  obtain ⟨hi, hj, hne⟩ := hij
  have e : ∀ c, (d.Lt r c : ℝ) * δ c =
      (if c = 2 * d.ci r then ((2 * (d.ctq (2 * d.ci r) - d.ctq (2 * d.cj r)) : ℚ) : ℝ) else 0) * δ c +
      (if c = 2 * d.ci r + 1 then ((2 * (d.ctq (2 * d.ci r + 1) - d.ctq (2 * d.cj r + 1)) : ℚ) : ℝ) else 0) * δ c +
      (if c = 2 * d.cj r then ((-(2 * (d.ctq (2 * d.ci r) - d.ctq (2 * d.cj r))) : ℚ) : ℝ) else 0) * δ c +
      (if c = 2 * d.cj r + 1 then ((-(2 * (d.ctq (2 * d.ci r + 1) - d.ctq (2 * d.cj r + 1))) : ℚ) : ℝ) else 0) *
        δ c := by
    intro c
    simp only [Lt, if_pos hr, Rat.cast_add, apply_ite (fun q : ℚ => (q : ℝ)), Rat.cast_zero]
    ring
  simp only [e, Finset.sum_add_distrib]
  rw [sum_ite_eq_mul (by omega), sum_ite_eq_mul (by omega), sum_ite_eq_mul (by omega),
    sum_ite_eq_mul (by omega)]
  push_cast
  ring

lemma Lt_bnd {r : ℕ} (hr : ¬ r < d.nC) (hb : d.bi (r - d.nC) < d.N) (δ : ℕ → ℝ) :
    ∑ c ∈ range (2 * d.N), (d.Lt r c : ℝ) * δ c =
      -2 * (d.ctq (2 * d.bi (r - d.nC)) : ℝ) * δ (2 * d.bi (r - d.nC)) -
      2 * (d.ctq (2 * d.bi (r - d.nC) + 1) : ℝ) * δ (2 * d.bi (r - d.nC) + 1) := by
  have e : ∀ c, (d.Lt r c : ℝ) * δ c =
      (if c = 2 * d.bi (r - d.nC) then (((-(2 * d.ctq (2 * d.bi (r - d.nC)))) : ℚ) : ℝ) else 0) * δ c +
      (if c = 2 * d.bi (r - d.nC) + 1 then (((-(2 * d.ctq (2 * d.bi (r - d.nC) + 1))) : ℚ) : ℝ) else 0) *
        δ c := by
    intro c
    simp only [Lt, if_neg hr, Rat.cast_add, apply_ite (fun q : ℚ => (q : ℝ)), Rat.cast_zero]
    ring
  simp only [e, Finset.sum_add_distrib]
  rw [sum_ite_eq_mul (by omega), sum_ite_eq_mul (by omega)]
  push_cast
  ring

end LUData

/-! ### The theorem -/

set_option maxHeartbeats 4000000 in
/-- **Local uniqueness from approximate data.** -/
theorem local_unique_gen (d : LUData) (hok : d.ok = true) (cs z : ℕ → ℝ) (P : ℝ)
    (hcs : ∀ c < 2 * d.N, |cs c - d.ctq c| ≤ d.rb)
    (hcon : ∀ r < d.nC, (cs (2 * d.ci r) - cs (2 * d.cj r)) ^ 2 +
      (cs (2 * d.ci r + 1) - cs (2 * d.cj r + 1)) ^ 2 = 4)
    (hbnd : ∀ t < d.nB, cs (2 * d.bi t) ^ 2 + cs (2 * d.bi t + 1) ^ 2 = P)
    (hgc : cs d.gauge = 0)
    (hzc : ∀ r < d.nC, 4 ≤ (z (2 * d.ci r) - z (2 * d.cj r)) ^ 2 +
      (z (2 * d.ci r + 1) - z (2 * d.cj r + 1)) ^ 2)
    (hzb : ∀ t < d.nB, z (2 * d.bi t) ^ 2 + z (2 * d.bi t + 1) ^ 2 ≤ P)
    (hzg : z d.gauge = 0)
    (hclose : ∑ c ∈ range (2 * d.N), (z c - cs c) ^ 2 < d.R2) :
    ∀ c < 2 * d.N, z c = cs c := by
  classical
  obtain ⟨hN, hg, -, hC, hB, hy, hW, hrb, hR2, htau, hfin⟩ := LUData.ok_spec hok
  set δ : ℕ → ℝ := fun c => z c - cs c with hδ
  set nd : ℝ := ∑ c ∈ range (2 * d.N), δ c ^ 2 with hnd
  have hnd0 : 0 ≤ nd := sum_nonneg (fun c _ => sq_nonneg _)
  set s : ℝ := Real.sqrt nd with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = nd := Real.sq_sqrt hnd0
  have hδs : ∀ c < 2 * d.N, |δ c| ≤ s := by
    intro c hc
    apply Real.abs_le_sqrt
    exact single_le_sum (f := fun c => δ c ^ 2) (fun c' _ => sq_nonneg (δ c')) (mem_range.mpr hc)
  have hrbR : (0 : ℝ) ≤ d.rb := by exact_mod_cast hrb
  -- the points
  set Pn : ℕ → ℝ := fun p => δ (2 * p) ^ 2 + δ (2 * p + 1) ^ 2 with hPn
  have hPn0 : ∀ p, 0 ≤ Pn p := fun p => by simp only [hPn]; positivity
  have hnd_pts : nd = ∑ p ∈ range d.N, Pn p := by rw [hnd, sum_two_mul]
  have hPn_pair : ∀ p q, p < d.N → q < d.N → p ≠ q → Pn p + Pn q ≤ nd := by
    intro p q hp hq hpq
    rw [hnd_pts]
    have hsub : ({p, q} : Finset ℕ) ⊆ range d.N := by
      intro x hx; simp at hx; rcases hx with rfl | rfl <;> simp [hp, hq]
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hPn0 x)
    rwa [Finset.sum_pair hpq] at this
  have hPn_le : ∀ p < d.N, Pn p ≤ nd := by
    intro p hp
    rw [hnd_pts]
    exact single_le_sum (fun q _ => hPn0 q) (mem_range.mpr hp)
  -- linear parts at `c*` and at `c̃`
  set ℓ : ℕ → ℝ := fun r => if r < d.nC then
      2 * (cs (2 * d.ci r) - cs (2 * d.cj r)) * (δ (2 * d.ci r) - δ (2 * d.cj r)) +
      2 * (cs (2 * d.ci r + 1) - cs (2 * d.cj r + 1)) * (δ (2 * d.ci r + 1) - δ (2 * d.cj r + 1))
    else -2 * cs (2 * d.bi (r - d.nC)) * δ (2 * d.bi (r - d.nC)) -
      2 * cs (2 * d.bi (r - d.nC) + 1) * δ (2 * d.bi (r - d.nC) + 1) with hℓ
  set ℓt : ℕ → ℝ := fun r => ∑ c ∈ range (2 * d.N), (d.Lt r c : ℝ) * δ c with hℓt
  have hcs' : ∀ c < 2 * d.N, |cs c - (d.ctq c : ℝ)| ≤ d.rb := hcs
  have hdℓ : ∀ r < d.nR, |ℓ r - ℓt r| ≤ 16 * d.rb * s := by
    intro r hr
    by_cases hrc : r < d.nC
    · obtain ⟨hi, hj, hne⟩ := hC r hrc
      simp only [hℓ, hℓt, if_pos hrc]
      rw [LUData.Lt_contact hrc ⟨hi, hj, hne⟩]
      have h1 := hcs' (2 * d.ci r) (by omega)
      have h2 := hcs' (2 * d.cj r) (by omega)
      have h3 := hcs' (2 * d.ci r + 1) (by omega)
      have h4 := hcs' (2 * d.cj r + 1) (by omega)
      have e1 := hδs (2 * d.ci r) (by omega)
      have e2 := hδs (2 * d.cj r) (by omega)
      have e3 := hδs (2 * d.ci r + 1) (by omega)
      have e4 := hδs (2 * d.cj r + 1) (by omega)
      set u1 := cs (2 * d.ci r) - (d.ctq (2 * d.ci r) : ℝ)
      set u2 := cs (2 * d.cj r) - (d.ctq (2 * d.cj r) : ℝ)
      set u3 := cs (2 * d.ci r + 1) - (d.ctq (2 * d.ci r + 1) : ℝ)
      set u4 := cs (2 * d.cj r + 1) - (d.ctq (2 * d.cj r + 1) : ℝ)
      have key : 2 * (cs (2 * d.ci r) - cs (2 * d.cj r)) * (δ (2 * d.ci r) - δ (2 * d.cj r)) +
          2 * (cs (2 * d.ci r + 1) - cs (2 * d.cj r + 1)) * (δ (2 * d.ci r + 1) - δ (2 * d.cj r + 1)) -
          (2 * ((d.ctq (2 * d.ci r) : ℝ) - d.ctq (2 * d.cj r)) * (δ (2 * d.ci r) - δ (2 * d.cj r)) +
          2 * ((d.ctq (2 * d.ci r + 1) : ℝ) - d.ctq (2 * d.cj r + 1)) * (δ (2 * d.ci r + 1) - δ (2 * d.cj r + 1)))
          = 2 * (u1 - u2) * (δ (2 * d.ci r) - δ (2 * d.cj r)) +
            2 * (u3 - u4) * (δ (2 * d.ci r + 1) - δ (2 * d.cj r + 1)) := by
        simp only [u1, u2, u3, u4]; ring
      rw [key]
      have b1 : |2 * (u1 - u2) * (δ (2 * d.ci r) - δ (2 * d.cj r))| ≤ 2 * (2 * d.rb) * (2 * s) := by
        rw [abs_mul, abs_mul]
        have : |u1 - u2| ≤ 2 * d.rb := le_trans (abs_sub _ _) (by linarith)
        have : |δ (2 * d.ci r) - δ (2 * d.cj r)| ≤ 2 * s := le_trans (abs_sub _ _) (by linarith)
        have h2' : |(2 : ℝ)| = 2 := abs_two
        rw [h2']
        gcongr
      have b2 : |2 * (u3 - u4) * (δ (2 * d.ci r + 1) - δ (2 * d.cj r + 1))| ≤ 2 * (2 * d.rb) * (2 * s) := by
        rw [abs_mul, abs_mul]
        have : |u3 - u4| ≤ 2 * d.rb := le_trans (abs_sub _ _) (by linarith)
        have : |δ (2 * d.ci r + 1) - δ (2 * d.cj r + 1)| ≤ 2 * s := le_trans (abs_sub _ _) (by linarith)
        have h2' : |(2 : ℝ)| = 2 := abs_two
        rw [h2']
        gcongr
      calc _ ≤ |2 * (u1 - u2) * (δ (2 * d.ci r) - δ (2 * d.cj r))| +
            |2 * (u3 - u4) * (δ (2 * d.ci r + 1) - δ (2 * d.cj r + 1))| := abs_add_le _ _
        _ ≤ 16 * d.rb * s := by nlinarith
    · have hb := hB (r - d.nC) (by unfold LUData.nR at hr; omega)
      simp only [hℓ, hℓt, if_neg hrc]
      rw [LUData.Lt_bnd hrc hb]
      have h1 := hcs' (2 * d.bi (r - d.nC)) (by omega)
      have h3 := hcs' (2 * d.bi (r - d.nC) + 1) (by omega)
      have e1 := hδs (2 * d.bi (r - d.nC)) (by omega)
      have e3 := hδs (2 * d.bi (r - d.nC) + 1) (by omega)
      set u1 := cs (2 * d.bi (r - d.nC)) - (d.ctq (2 * d.bi (r - d.nC)) : ℝ)
      set u3 := cs (2 * d.bi (r - d.nC) + 1) - (d.ctq (2 * d.bi (r - d.nC) + 1) : ℝ)
      have key : -2 * cs (2 * d.bi (r - d.nC)) * δ (2 * d.bi (r - d.nC)) -
          2 * cs (2 * d.bi (r - d.nC) + 1) * δ (2 * d.bi (r - d.nC) + 1) -
          (-2 * (d.ctq (2 * d.bi (r - d.nC)) : ℝ) * δ (2 * d.bi (r - d.nC)) -
          2 * (d.ctq (2 * d.bi (r - d.nC) + 1) : ℝ) * δ (2 * d.bi (r - d.nC) + 1)) =
          -2 * u1 * δ (2 * d.bi (r - d.nC)) - 2 * u3 * δ (2 * d.bi (r - d.nC) + 1) := by
        simp only [u1, u3]; ring
      rw [key]
      have b1 : |-2 * u1 * δ (2 * d.bi (r - d.nC))| ≤ 2 * d.rb * s := by
        rw [abs_mul, abs_mul, abs_neg, abs_two]; gcongr
      have b3 : |2 * u3 * δ (2 * d.bi (r - d.nC) + 1)| ≤ 2 * d.rb * s := by
        rw [abs_mul, abs_mul, abs_two]; gcongr
      calc _ ≤ |-2 * u1 * δ (2 * d.bi (r - d.nC))| + |2 * u3 * δ (2 * d.bi (r - d.nC) + 1)| := abs_sub _ _
        _ ≤ 16 * d.rb * s := by nlinarith
  -- the constraint slacks
  set qd : ℕ → ℝ := fun r => if r < d.nC then
      (δ (2 * d.ci r) - δ (2 * d.cj r)) ^ 2 + (δ (2 * d.ci r + 1) - δ (2 * d.cj r + 1)) ^ 2
    else -Pn (d.bi (r - d.nC)) with hqd
  set g : ℕ → ℝ := fun r => ℓ r + qd r with hgdef
  have hg0 : ∀ r < d.nR, 0 ≤ g r := by
    intro r hr
    by_cases hrc : r < d.nC
    · have h4 := hcon r hrc
      have hz := hzc r hrc
      simp only [hgdef, hℓ, hqd, if_pos hrc, hδ]
      nlinarith [h4, hz]
    · have ht : r - d.nC < d.nB := by unfold LUData.nR at hr; omega
      have h4 := hbnd (r - d.nC) ht
      have hz := hzb (r - d.nC) ht
      simp only [hgdef, hℓ, hqd, if_neg hrc, hδ, hPn]
      nlinarith [h4, hz]
  -- the stress
  set y : ℕ → ℝ := fun r => (d.yq r : ℝ) with hydef
  have hy0 : ∀ r < d.nR, 0 < y r := fun r hr => by
    simp only [hydef]; exact_mod_cast hy r hr
  have hstress_t : ∑ r ∈ range d.nR, y r * ℓt r = ∑ c ∈ range (2 * d.N), (d.eps c : ℝ) * δ c := by
    simp only [hydef, hℓt, Finset.mul_sum, LUData.eps]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    ring
  have hstress : |∑ r ∈ range d.nR, y r * ℓ r| ≤ (d.eta : ℝ) * s := by
    have e : ∑ r ∈ range d.nR, y r * ℓ r =
        ∑ r ∈ range d.nR, y r * ℓt r + ∑ r ∈ range d.nR, y r * (ℓ r - ℓt r) := by
      rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro r _; ring
    rw [e, hstress_t]
    have b1 : |∑ c ∈ range (2 * d.N), (d.eps c : ℝ) * δ c| ≤
        (∑ c ∈ range (2 * d.N), |(d.eps c : ℝ)|) * s := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro c hc
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hδs c (mem_range.mp hc)) (abs_nonneg _)
    have b2 : |∑ r ∈ range d.nR, y r * (ℓ r - ℓt r)| ≤ 16 * d.rb * (∑ r ∈ range d.nR, y r) * s := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro r hr
      have hr' := mem_range.mp hr
      rw [abs_mul, abs_of_pos (hy0 r hr')]
      have := hdℓ r hr'
      have := hy0 r hr'
      nlinarith
    have heta : (d.eta : ℝ) = ∑ c ∈ range (2 * d.N), |(d.eps c : ℝ)| + 16 * d.rb * ∑ r ∈ range d.nR, y r := by
      simp only [LUData.eta, hydef]; push_cast; rfl
    rw [heta]
    calc _ ≤ |∑ c ∈ range (2 * d.N), (d.eps c : ℝ) * δ c| + |∑ r ∈ range d.nR, y r * (ℓ r - ℓt r)| :=
          abs_add_le _ _
      _ ≤ _ := by nlinarith
  -- the quadratic part, weighted by the stress, is at most `qbar * nd`
  have hQc : ∀ r < d.nC, qd r ≤ 2 * (Pn (d.ci r) + Pn (d.cj r)) := by
    intro r hr
    simp only [hqd, if_pos hr, hPn]
    nlinarith [sq_nonneg (δ (2 * d.ci r) + δ (2 * d.cj r)),
      sq_nonneg (δ (2 * d.ci r + 1) + δ (2 * d.cj r + 1))]
  have hregroup : ∀ (w : ℕ → ℝ) (F : ℕ → ℝ),
      ∑ r ∈ range d.nC, w r * (F (d.ci r) + F (d.cj r)) =
        ∑ p ∈ range d.N, F p * ∑ r ∈ range d.nC,
          ((if d.ci r = p then w r else 0) + (if d.cj r = p then w r else 0)) := by
    intro w F
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r hr
    obtain ⟨hi, hj, -⟩ := hC r (mem_range.mp hr)
    rw [mul_add, Finset.sum_congr rfl (fun p _ => by rw [mul_add]), Finset.sum_add_distrib]
    have e1 : ∑ p ∈ range d.N, F p * (if d.ci r = p then w r else 0) = w r * F (d.ci r) := by
      rw [Finset.sum_eq_single (d.ci r)]
      · simp; ring
      · intro b _ hb; simp [Ne.symm hb]
      · intro h; exact absurd (mem_range.mpr hi) h
    have e2 : ∑ p ∈ range d.N, F p * (if d.cj r = p then w r else 0) = w r * F (d.cj r) := by
      rw [Finset.sum_eq_single (d.cj r)]
      · simp; ring
      · intro b _ hb; simp [Ne.symm hb]
      · intro h; exact absurd (mem_range.mpr hj) h
    rw [e1, e2]
  have hyq : ∑ r ∈ range d.nR, y r * qd r ≤ (d.qbar : ℝ) * nd := by
    have hsplit : ∑ r ∈ range d.nR, y r * qd r =
        ∑ r ∈ range d.nC, y r * qd r + ∑ r ∈ Finset.Ico d.nC d.nR, y r * qd r :=
      (Finset.sum_range_add_sum_Ico _ (by unfold LUData.nR; omega)).symm
    have hneg : ∑ r ∈ Finset.Ico d.nC d.nR, y r * qd r ≤ 0 := by
      apply Finset.sum_nonpos
      intro r hr
      rw [Finset.mem_Ico] at hr
      simp only [hqd, if_neg (show ¬ r < d.nC by omega)]
      have := hy0 r hr.2
      have := hPn0 (d.bi (r - d.nC))
      nlinarith
    have hcont : ∑ r ∈ range d.nC, y r * qd r ≤
        ∑ r ∈ range d.nC, (2 * y r) * (Pn (d.ci r) + Pn (d.cj r)) := by
      apply Finset.sum_le_sum
      intro r hr
      have hr' := mem_range.mp hr
      have := hQc r hr'
      have := hy0 r (by unfold LUData.nR; omega)
      nlinarith
    rw [hregroup] at hcont
    have hw : ∀ p ∈ range d.N, Pn p * ∑ r ∈ range d.nC,
        ((if d.ci r = p then 2 * y r else 0) + (if d.cj r = p then 2 * y r else 0)) ≤ Pn p * d.qbar := by
      intro p hp
      apply mul_le_mul_of_nonneg_left _ (hPn0 p)
      have hwp := hW p (mem_range.mp hp)
      have hwR : ((2 * d.wt p : ℚ) : ℝ) ≤ (d.qbar : ℝ) := by exact_mod_cast hwp
      refine le_trans (le_of_eq ?_) hwR
      simp only [LUData.wt, hydef]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      split_ifs <;> ring
    have := Finset.sum_le_sum hw
    rw [← Finset.sum_mul, ← hnd_pts] at this
    linarith
  -- the weighted slacks
  have hyg : ∑ r ∈ range d.nR, y r * g r ≤ (d.eta : ℝ) * s + d.qbar * nd := by
    have e : ∑ r ∈ range d.nR, y r * g r = ∑ r ∈ range d.nR, y r * ℓ r + ∑ r ∈ range d.nR, y r * qd r := by
      rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro r _; simp only [hgdef]; ring
    rw [e]
    have := le_abs_self (∑ r ∈ range d.nR, y r * ℓ r)
    linarith
  have hgsmall : ∀ r < d.nR, y r * g r ≤ (d.eta : ℝ) * s + d.qbar * nd := by
    intro r hr
    have hsingle : y r * g r ≤ ∑ r' ∈ range d.nR, y r' * g r' :=
      single_le_sum (f := fun r' => y r' * g r') (fun r' hr' => mul_nonneg (hy0 r' (mem_range.mp hr')).le
        (hg0 r' (mem_range.mp hr'))) (mem_range.mpr hr)
    linarith
  -- each linear part is small
  have hℓsmall : ∀ r < d.nR, |ℓ r| ≤ (d.eta / d.yq r : ℚ) * s + (d.arow r : ℝ) * nd := by
    intro r hr
    have hyr := hy0 r hr
    have hgs := hgsmall r hr
    have hg0r := hg0 r hr
    have hgle : g r ≤ ((d.eta : ℝ) * s + d.qbar * nd) / y r := by
      rw [le_div_iff₀ hyr]; linarith
    have hdiv : ((d.eta : ℝ) * s + d.qbar * nd) / y r = (d.eta / d.yq r : ℚ) * s + (d.qbar / d.yq r : ℚ) * nd := by
      simp only [hydef]; push_cast; field_simp
    have hqy0 : (0 : ℝ) ≤ (d.qbar / d.yq r : ℚ) := by
      have : (0 : ℚ) ≤ d.qbar := by
        have := hW 0 hN
        have hw0 : 0 ≤ d.wt 0 := by
          unfold LUData.wt
          apply Finset.sum_nonneg; intro r' hr'
          have := hy r' (by have := mem_range.mp hr'; unfold LUData.nR; omega)
          split_ifs <;> linarith
        linarith
      have : (0 : ℚ) ≤ d.qbar / d.yq r := div_nonneg this (hy r hr).le
      exact_mod_cast this
    have hes0 : (0 : ℝ) ≤ (d.eta / d.yq r : ℚ) * s := by
      apply mul_nonneg _ hs0
      have heta0 : (0 : ℚ) ≤ d.eta := by
        unfold LUData.eta
        apply add_nonneg (Finset.sum_nonneg (fun c _ => abs_nonneg _))
        exact mul_nonneg (mul_nonneg (by norm_num) hrb)
          (Finset.sum_nonneg (fun r' hr' => (hy r' (mem_range.mp hr')).le))
      have : (0 : ℚ) ≤ d.eta / d.yq r := div_nonneg heta0 (hy r hr).le
      exact_mod_cast this
    by_cases hrc : r < d.nC
    · obtain ⟨hi, hj, hne⟩ := hC r hrc
      have hq0 : 0 ≤ qd r := by simp only [hqd, if_pos hrc]; positivity
      have hq2 : qd r ≤ 2 * nd := le_trans (hQc r hrc) (by linarith [hPn_pair _ _ hi hj hne])
      have ha : ((d.arow r : ℚ) : ℝ) = max 2 ((d.qbar / d.yq r : ℚ) : ℝ) := by
        simp only [LUData.arow, if_pos hrc]; push_cast; rfl
      rw [ha, abs_le]
      have hm1 : (2 : ℝ) ≤ max 2 ((d.qbar / d.yq r : ℚ) : ℝ) := le_max_left _ _
      have hm2 : ((d.qbar / d.yq r : ℚ) : ℝ) ≤ max 2 ((d.qbar / d.yq r : ℚ) : ℝ) := le_max_right _ _
      have hgq : g r = ℓ r + qd r := rfl
      constructor
      · nlinarith
      · nlinarith
    · have ht : r - d.nC < d.nB := by unfold LUData.nR at hr; omega
      have hb := hB (r - d.nC) ht
      have hPb := hPn_le (d.bi (r - d.nC)) hb
      have hPb0 := hPn0 (d.bi (r - d.nC))
      have ha : ((d.arow r : ℚ) : ℝ) = ((d.qbar / d.yq r : ℚ) : ℝ) + 1 := by
        simp only [LUData.arow, if_neg hrc]; push_cast; ring
      rw [ha, abs_le]
      have hgq : g r = ℓ r + qd r := rfl
      have hqb : qd r = -Pn (d.bi (r - d.nC)) := by simp only [hqd, if_neg hrc]
      constructor
      · nlinarith
      · nlinarith
  have hℓsq : ∑ r ∈ range d.nR, ℓ r ^ 2 ≤ 2 * (d.H2 : ℝ) * nd + 2 * (d.K2 : ℝ) * nd ^ 2 := by
    have hH : (d.H2 : ℝ) = ∑ r ∈ range d.nR, ((d.eta / d.yq r : ℚ) : ℝ) ^ 2 := by
      simp only [LUData.H2]; push_cast; rfl
    have hK : (d.K2 : ℝ) = ∑ r ∈ range d.nR, ((d.arow r : ℚ) : ℝ) ^ 2 := by
      simp only [LUData.K2]; push_cast; rfl
    have hpt : ∀ r ∈ range d.nR, ℓ r ^ 2 ≤
        2 * ((d.eta / d.yq r : ℚ) : ℝ) ^ 2 * nd + 2 * ((d.arow r : ℚ) : ℝ) ^ 2 * nd ^ 2 := by
      intro r hr
      have h := hℓsmall r (mem_range.mp hr)
      have h2 : ℓ r ^ 2 ≤ (((d.eta / d.yq r : ℚ) : ℝ) * s + (d.arow r : ℝ) * nd) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
      have h3 : (((d.eta / d.yq r : ℚ) : ℝ) * s + (d.arow r : ℝ) * nd) ^ 2 ≤
          2 * (((d.eta / d.yq r : ℚ) : ℝ) * s) ^ 2 + 2 * ((d.arow r : ℝ) * nd) ^ 2 := by
        nlinarith [sq_nonneg (((d.eta / d.yq r : ℚ) : ℝ) * s - (d.arow r : ℝ) * nd)]
      have h4 : (((d.eta / d.yq r : ℚ) : ℝ) * s) ^ 2 = ((d.eta / d.yq r : ℚ) : ℝ) ^ 2 * nd := by
        rw [mul_pow, hss]
      rw [h4] at h3
      nlinarith
    calc ∑ r ∈ range d.nR, ℓ r ^ 2
        ≤ ∑ r ∈ range d.nR, (2 * ((d.eta / d.yq r : ℚ) : ℝ) ^ 2 * nd +
            2 * ((d.arow r : ℚ) : ℝ) ^ 2 * nd ^ 2) := Finset.sum_le_sum hpt
      _ = 2 * (∑ r ∈ range d.nR, ((d.eta / d.yq r : ℚ) : ℝ) ^ 2) * nd +
            2 * (∑ r ∈ range d.nR, ((d.arow r : ℚ) : ℝ) ^ 2) * nd ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum,
            ← Finset.mul_sum]
      _ = _ := by rw [hH, hK]
  -- the left inverse
  have hδg : δ d.gauge = 0 := by simp only [hδ, hzg, hgc]; ring
  set δf : ℕ → ℝ := fun i => δ (if i < d.gauge then i else i + 1) with hδf
  have hnd_free : nd = ∑ i ∈ range d.nF, δf i ^ 2 := by
    rw [hnd, sum_free hg (fun c => δ c ^ 2), hδg]
    simp only [hδf, LUData.nF]
    ring
  set A : ℕ → ℝ := fun i => ∑ r ∈ range d.nR, (d.Mq i r : ℝ) * ℓ r with hAdef
  set B : ℕ → ℝ := fun i => ∑ r ∈ range d.nR, (d.Mq i r : ℝ) * (ℓ r - ℓt r) with hBdef
  set C : ℕ → ℝ := fun i => ∑ j ∈ range d.nF, (d.Eq i j : ℝ) * δf j with hCdef
  have hinv : ∀ i < d.nF, δf i = A i - B i - C i := by
    intro i hi
    have h1 : ∑ r ∈ range d.nR, (d.Mq i r : ℝ) * ℓt r = δf i + C i := by
      have e : ∑ r ∈ range d.nR, (d.Mq i r : ℝ) * ℓt r =
          ∑ c ∈ range (2 * d.N), (∑ r ∈ range d.nR, (d.Mq i r : ℝ) * (d.Lt r c : ℝ)) * δ c := by
        simp only [hℓt, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro c _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro r _
        ring
      rw [e, sum_free hg, hδg, mul_zero, zero_add]
      have e2 : ∀ j, (∑ r ∈ range d.nR, (d.Mq i r : ℝ) * (d.Lt r (if j < d.gauge then j else j + 1) : ℝ)) =
          (d.Eq i j : ℝ) + (if i = j then 1 else 0) := by
        intro j
        simp only [LUData.Eq, LUData.fcol]
        push_cast
        split_ifs <;> ring
      simp only [e2, add_mul, Finset.sum_add_distrib]
      have e3 : ∑ x ∈ range (2 * d.N - 1), (if i = x then (1 : ℝ) else 0) * δ (if x < d.gauge then x else x + 1) =
          δf i := by
        rw [Finset.sum_eq_single i]
        · simp [hδf]
        · intro b _ hb; simp [Ne.symm hb]
        · intro h; exact absurd (mem_range.mpr (by simpa [LUData.nF] using hi)) h
      rw [e3]
      simp only [hCdef, hδf, LUData.nF]
      ring
    have h2 : ∑ r ∈ range d.nR, (d.Mq i r : ℝ) * ℓt r = A i - B i := by
      simp only [hAdef, hBdef, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro r _; ring
    linarith
  -- the three error terms
  have hMF : (d.MF2 : ℝ) = ∑ i ∈ range d.nF, ∑ r ∈ range d.nR, (d.Mq i r : ℝ) ^ 2 := by
    simp only [LUData.MF2]; push_cast; rfl
  have hEF : (d.EF2 : ℝ) = ∑ i ∈ range d.nF, ∑ j ∈ range d.nF, (d.Eq i j : ℝ) ^ 2 := by
    simp only [LUData.EF2]; push_cast; rfl
  have hAs : ∑ i ∈ range d.nF, A i ^ 2 ≤ (d.MF2 : ℝ) * ∑ r ∈ range d.nR, ℓ r ^ 2 := by
    rw [hMF, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hBs : ∑ i ∈ range d.nF, B i ^ 2 ≤ (d.MF2 : ℝ) * (d.nR * (16 * d.rb * s) ^ 2) := by
    have hd2 : ∑ r ∈ range d.nR, (ℓ r - ℓt r) ^ 2 ≤ d.nR * (16 * d.rb * s) ^ 2 := by
      have : ∑ r ∈ range d.nR, (ℓ r - ℓt r) ^ 2 ≤ ∑ r ∈ range d.nR, (16 * (d.rb : ℝ) * s) ^ 2 := by
        apply Finset.sum_le_sum
        intro r hr
        have h := hdℓ r (mem_range.mp hr)
        have h0 : (0 : ℝ) ≤ 16 * d.rb * s := by positivity
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h 2
      simpa using this
    have hMs : ∑ i ∈ range d.nF, B i ^ 2 ≤ (d.MF2 : ℝ) * ∑ r ∈ range d.nR, (ℓ r - ℓt r) ^ 2 := by
      rw [hMF, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have hMF0 : (0 : ℝ) ≤ d.MF2 := by rw [hMF]; positivity
    exact le_trans hMs (mul_le_mul_of_nonneg_left hd2 hMF0)
  have hCs : ∑ i ∈ range d.nF, C i ^ 2 ≤ (d.EF2 : ℝ) * nd := by
    rw [hEF, hnd_free, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hsum : nd ≤ 3 * (∑ i ∈ range d.nF, A i ^ 2 + ∑ i ∈ range d.nF, B i ^ 2 +
      ∑ i ∈ range d.nF, C i ^ 2) := by
    rw [hnd_free, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [hinv i (mem_range.mp hi)]
    nlinarith [sq_nonneg (A i - B i), sq_nonneg (A i - C i), sq_nonneg (B i - C i),
      sq_nonneg (A i + B i), sq_nonneg (A i + C i), sq_nonneg (B i + C i)]
  -- the main inequality
  have htauR : (d.tau : ℝ) = 6 * d.MF2 * d.H2 + 768 * d.MF2 * d.nR * d.rb ^ 2 + 3 * d.EF2 := by
    simp only [LUData.tau]; push_cast; ring
  have hMF0 : (0 : ℝ) ≤ d.MF2 := by rw [hMF]; positivity
  have hK0 : (0 : ℝ) ≤ d.K2 := by
    have : (d.K2 : ℝ) = ∑ r ∈ range d.nR, ((d.arow r : ℚ) : ℝ) ^ 2 := by
      simp only [LUData.K2]; push_cast; rfl
    rw [this]; positivity
  have hmain : nd ≤ (d.tau : ℝ) * nd + 6 * d.MF2 * d.K2 * nd ^ 2 := by
    have hA' := mul_le_mul_of_nonneg_left hℓsq hMF0
    have hs2 : (16 * (d.rb : ℝ) * s) ^ 2 = 256 * d.rb ^ 2 * nd := by rw [← hss]; ring
    rw [hs2] at hBs
    rw [htauR]
    nlinarith
  have hnd_zero : nd = 0 := by
    by_contra hne
    have hpos : 0 < nd := lt_of_le_of_ne hnd0 (Ne.symm hne)
    have ht : (d.tau : ℝ) ≤ 1 / 2 := by
      have := (Rat.cast_le (K := ℝ)).mpr htau
      push_cast at this
      exact this
    have h1 : nd ≤ 12 * d.MF2 * d.K2 * nd ^ 2 := by nlinarith
    have h2 : 1 ≤ 12 * (d.MF2 : ℝ) * d.K2 * nd := by
      have : nd * 1 ≤ nd * (12 * d.MF2 * d.K2 * nd) := by nlinarith
      exact le_of_mul_le_mul_left this hpos
    have hfinR : (12 : ℝ) * d.R2 * d.MF2 * d.K2 ≤ 1 := by exact_mod_cast hfin
    have hMK : 0 ≤ (d.MF2 : ℝ) * d.K2 := mul_nonneg hMF0 hK0
    nlinarith
  intro c hc
  have hc2 : δ c ^ 2 ≤ nd := single_le_sum (f := fun c => δ c ^ 2) (fun c' _ => sq_nonneg (δ c')) (mem_range.mpr hc)
  rw [hnd_zero] at hc2
  have : δ c = 0 := by nlinarith [sq_nonneg (δ c)]
  simp only [hδ] at this
  linarith

end CirclePacking
