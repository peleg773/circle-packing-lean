import Mathlib
import C15Compute
import CirclePacking.CosTurn

/-!
# The greedy bound for points on a circle avoiding forbidden arcs

Angles are measured in turns (the circle is `ℝ / ℤ`).  Arc endpoints are integers in units of
`1/S` turns: a *forbidden arc* `p = (l, h)` stands for the open intervals `(l/S + m, h/S + m)`, `m ∈ ℤ`.
The functions `jump`, `greedyAux`, `liftArcs`, `greedyBound` are defined in `C15Compute`.
-/

namespace CirclePacking

/-- the real number represented by an integer in units of `1/S` -/
noncomputable def sc (x : ℤ) : ℝ := (x : ℝ) / (S : ℝ)

lemma sc_add (x y : ℤ) : sc (x + y) = sc x + sc y := by unfold sc; push_cast; ring
lemma sc_sub (x y : ℤ) : sc (x - y) = sc x - sc y := by unfold sc; push_cast; ring
lemma sc_S : sc S = 1 := by unfold sc; field_simp [S_pos.ne']
lemma sc_le_iff {x y : ℤ} : sc x ≤ sc y ↔ x ≤ y := by
  unfold sc; rw [div_le_div_iff_of_pos_right S_pos]; exact_mod_cast Iff.rfl
lemma sc_lt_iff {x y : ℤ} : sc x < sc y ↔ x < y := by
  unfold sc; rw [div_lt_div_iff_of_pos_right S_pos]; exact_mod_cast Iff.rfl

/-- `x` avoids all integer translates of the open interval `(p.1/S, p.2/S)`. -/
def Avoids (x : ℝ) (p : ℤ × ℤ) : Prop := ∀ m : ℤ, ¬ ((sc p.1 + m < x) ∧ (x < sc p.2 + m))

lemma Avoids.shift {x : ℝ} {p : ℤ × ℤ} (h : Avoids x p) (k : ℤ) : Avoids (x + k) p := by
  intro m hm
  apply h (m - k)
  push_cast
  constructor <;> linarith [hm.1, hm.2]

lemma jump_le (A : List (ℤ × ℤ)) (y : ℝ) (hy : ∀ p ∈ A, ¬ ((sc p.1 < y) ∧ (y < sc p.2))) :
    ∀ (f : ℕ) (z : ℤ), sc z ≤ y → sc (jump A f z) ≤ y
  | 0, z, hz => by simpa [jump] using hz
  | f + 1, z, hz => by
    simp only [jump]
    cases h : A.find? (fun p => decide (p.1 < z ∧ z < p.2)) with
    | none => simpa using hz
    | some p =>
      simp only
      have hp := List.find?_some h
      have hmem := List.mem_of_find?_eq_some h
      simp only [decide_eq_true_eq] at hp
      apply jump_le A y hy f p.2
      have h1 : sc p.1 < sc z := sc_lt_iff.mpr hp.1
      by_contra hc
      push Not at hc
      exact hy p hmem ⟨by linarith, hc⟩

/-- `x :: ys` is a chain with consecutive gaps at least `δ`. -/
def GapChain (δ : ℝ) (x : ℝ) (ys : List ℝ) : Prop := List.IsChain (fun u v => u + δ ≤ v) (x :: ys)

lemma gapChain_cons {δ x y : ℝ} {ys : List ℝ} :
    GapChain δ x (y :: ys) ↔ x + δ ≤ y ∧ GapChain δ y ys := by
  simp [GapChain, List.isChain_cons_cons]

lemma GapChain.mono {δ : ℝ} {x x' : ℝ} (hx : x' ≤ x) {ys : List ℝ} (h : GapChain δ x ys) :
    GapChain δ x' ys := by
  cases ys with
  | nil => simp [GapChain]
  | cons y ys =>
    rw [gapChain_cons] at h ⊢
    exact ⟨by linarith [h.1], h.2⟩

lemma greedyAux_ge (A : List (ℤ × ℤ)) (δ lim : ℤ) (jf : ℕ) :
    ∀ (ys : List ℝ) (f : ℕ) (x : ℤ), ys.length ≤ f →
      (∀ y ∈ ys, ∀ p ∈ A, ¬ ((sc p.1 < y) ∧ (y < sc p.2))) →
      GapChain (sc δ) (sc x) ys →
      (∀ y ∈ ys, y ≤ sc lim) →
      ys.length ≤ greedyAux A δ lim jf f x
  | [], _, _, _, _, _, _ => by simp
  | y :: ys, 0, _, hl, _, _, _ => by simp at hl
  | y :: ys, f + 1, x, hl, hA, hc, hlim => by
    rw [gapChain_cons] at hc
    have hz : sc (jump A jf (x + δ)) ≤ y := by
      apply jump_le A y (hA y (by simp)) jf (x + δ)
      rw [sc_add]; linarith [hc.1]
    have hzl : jump A jf (x + δ) ≤ lim := sc_le_iff.mp (le_trans hz (hlim y (by simp)))
    simp only [greedyAux, hzl, ite_true]
    have ih := greedyAux_ge A δ lim jf ys f (jump A jf (x + δ)) (by simpa using hl)
      (fun y' hy' => hA y' (by simp [hy'])) (hc.2.mono hz)
      (fun y' hy' => hlim y' (by simp [hy']))
    simp only [List.length_cons]
    omega

/-- Cyclic sorting: starting from the point `a b0`, the other points (moved by integers into
`[a b0, a b0 + 1)`) form a chain with gaps `≥ δ`, ending at most at `a b0 + 1 - δ`. -/
lemma exists_chain {B : ℕ} (a : Fin B → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ b b', b ≠ b' → ∀ m : ℤ, δ ≤ |a b - a b' - m|) (b0 : Fin B) :
    ∃ ys : List ℝ, ys.length = B - 1 ∧ GapChain δ (a b0) ys ∧
      (∀ y ∈ ys, y ≤ a b0 + 1 - δ) ∧ (∀ y ∈ ys, ∃ b, ∃ m : ℤ, y = a b + m) := by
  classical
  set x0 := a b0 with hx0
  let r : Fin B → ℝ := fun b => a b - ⌊a b - x0⌋
  have hr_range : ∀ b, x0 ≤ r b ∧ r b < x0 + 1 := by
    intro b
    have h1 := Int.floor_le (a b - x0)
    have h2 := Int.lt_floor_add_one (a b - x0)
    constructor <;> simp only [r] <;> linarith
  have hr_sep : ∀ b b', b ≠ b' → ∀ m : ℤ, δ ≤ |r b - r b' - m| := by
    intro b b' hbb' m
    have := hsep b b' hbb' (m + ⌊a b - x0⌋ - ⌊a b' - x0⌋)
    simp only [r]
    push_cast at this
    have e : a b - ↑⌊a b - x0⌋ - (a b' - ↑⌊a b' - x0⌋) - ↑m
        = a b - a b' - (↑m + ↑⌊a b - x0⌋ - ↑⌊a b' - x0⌋) := by ring
    rw [e]; exact this
  have hr0 : r b0 = x0 := by simp [r, hx0]
  have hinj : Function.Injective r := by
    intro b b' h
    by_contra hne
    have := hr_sep b b' hne 0
    rw [h] at this
    simp at this
    linarith
  set Sset := (Finset.univ.erase b0).image r with hS
  have hmemS : ∀ y, y ∈ Sset ↔ ∃ b, b ≠ b0 ∧ r b = y := by
    intro y
    simp [hS, Finset.mem_image, Finset.mem_erase]
  refine ⟨Sset.sort (· ≤ ·), ?_, ?_, ?_, ?_⟩
  · rw [Finset.length_sort, Finset.card_image_of_injective _ hinj,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  · unfold GapChain
    apply List.Pairwise.isChain
    rw [List.pairwise_cons]
    constructor
    · intro y hy
      rw [Finset.mem_sort, hmemS] at hy
      obtain ⟨b, hne, rfl⟩ := hy
      have h1 := hr_sep b b0 hne 0
      rw [hr0] at h1
      simp only [Int.cast_zero, sub_zero] at h1
      have := (hr_range b).1
      rw [abs_of_nonneg (by linarith)] at h1
      linarith
    · have hp := (Finset.pairwise_sort Sset (· ≤ ·)).and (Finset.sort_nodup Sset (· ≤ ·))
      refine hp.imp_of_mem ?_
      intro u v hu hv huv
      rw [Finset.mem_sort, hmemS] at hu hv
      obtain ⟨b, -, rfl⟩ := hu
      obtain ⟨b', -, rfl⟩ := hv
      have hbb : b' ≠ b := by
        intro h; rw [h] at huv; exact huv.2 rfl
      have h1 := hr_sep b' b hbb 0
      simp only [Int.cast_zero, sub_zero] at h1
      rw [abs_of_nonneg (by linarith [huv.1])] at h1
      linarith
  · intro y hy
    rw [Finset.mem_sort, hmemS] at hy
    obtain ⟨b, hne, rfl⟩ := hy
    have h1 := hr_sep b b0 hne 1
    rw [hr0] at h1
    have := (hr_range b).2
    simp only [Int.cast_one] at h1
    rw [abs_of_neg (by linarith)] at h1
    linarith
  · intro y hy
    rw [Finset.mem_sort, hmemS] at hy
    obtain ⟨b, -, rfl⟩ := hy
    exact ⟨b, -⌊a b - x0⌋, by simp [r]; ring⟩

/-- Rotation argument: rotating all points clockwise by a suitable `τ ≥ 0` keeps them allowed and
puts one of them on the right end of a forbidden arc. -/
lemma rotation (base : List (ℤ × ℤ)) (hb : base ≠ []) {B : ℕ} (hB : 0 < B) (a : Fin B → ℝ)
    (hall : ∀ b, ∀ p ∈ base, Avoids (a b) p) :
    ∃ τ : ℝ, 0 ≤ τ ∧ ∃ p ∈ base, ∃ b0 : Fin B, ∃ m : ℤ, a b0 - τ = sc p.2 + m ∧
      ∀ b, ∀ p ∈ base, Avoids (a b - τ) p := by
  classical
  let d : Fin B × (ℤ × ℤ) → ℝ := fun q => a q.1 - sc q.2.2 - (⌈a q.1 - sc q.2.1⌉ - 1)
  have hd0 : ∀ b, ∀ p ∈ base, 0 ≤ d (b, p) := by
    intro b p hp
    have h1 := Int.ceil_lt_add_one (a b - sc p.1)
    have hav := hall b p hp (⌈a b - sc p.1⌉ - 1)
    push_cast at hav
    simp only [d]
    by_contra hc
    exact hav ⟨by linarith, by linarith⟩
  have hne : ((Finset.univ : Finset (Fin B)) ×ˢ base.toFinset).Nonempty := by
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil base hb
    exact ⟨(⟨0, hB⟩, p), by simp [hp]⟩
  obtain ⟨⟨b0, p0⟩, hmem, hmin⟩ := Finset.exists_min_image _ d hne
  simp only [Finset.mem_product, Finset.mem_univ, List.mem_toFinset, true_and] at hmem
  refine ⟨d (b0, p0), hd0 b0 p0 hmem, p0, hmem, b0, ⌈a b0 - sc p0.1⌉ - 1, ?_, ?_⟩
  · simp only [d]; push_cast; ring
  · intro b p hp m hm
    have hmin' := hmin (b, p) (by simp [hp])
    have hτ := hd0 b0 p0 hmem
    have hm1 : (m : ℝ) < a b - sc p.1 := by linarith [hm.1]
    have hm2 : m ≤ ⌈a b - sc p.1⌉ - 1 := by
      have : m < ⌈a b - sc p.1⌉ := by
        rw [← Int.cast_lt (R := ℝ)]
        exact lt_of_lt_of_le hm1 (Int.le_ceil _)
      omega
    have hm3 : (m : ℝ) ≤ ⌈a b - sc p.1⌉ - 1 := by exact_mod_cast hm2
    simp only [d] at hmin'
    linarith [hm.2]

lemma avoids_lift {base : List (ℤ × ℤ)} {y : ℝ} (h : ∀ p ∈ base, Avoids y p) :
    ∀ p ∈ liftArcs base, ¬ ((sc p.1 < y) ∧ (y < sc p.2)) := by
  intro p hp
  simp only [liftArcs, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hp
  obtain ⟨q, hq, hpq⟩ := hp
  have hy := h q hq
  have e1 : ∀ x : ℤ, sc (x - S) = sc x + ((-1 : ℤ) : ℝ) := by
    intro x; rw [sc_sub, sc_S]; push_cast; ring
  have e2 : ∀ x : ℤ, sc (x + S) = sc x + ((1 : ℤ) : ℝ) := by
    intro x; rw [sc_add, sc_S]; push_cast; ring
  have e3 : ∀ x : ℤ, sc (x + 2 * S) = sc x + ((2 : ℤ) : ℝ) := by
    intro x; rw [sc_add]; unfold sc; push_cast; field_simp [S_pos.ne']
  rcases hpq with rfl | rfl | rfl | rfl
  · simp only [e1]; exact hy (-1)
  · have := hy 0; simpa using this
  · simp only [e2]; exact hy 1
  · simp only [e3]; exact hy 2

lemma le_foldr_max {l : List ℕ} {x : ℕ} (hx : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

/-- **Greedy bound.**  `B` points on the circle with pairwise (circular) distance `≥ δ/S` avoiding all
integer translates of the open arcs of `base` number at most `greedyBound base δ jf f`
(provided the fuel `f` is at least `B - 1`). -/
theorem card_le_greedyBound (base : List (ℤ × ℤ)) (δ : ℤ) (hδ : 0 < δ) (jf f : ℕ) {B : ℕ}
    (hBf : B ≤ f + 1) (a : Fin B → ℝ)
    (hsep : ∀ b b', b ≠ b' → ∀ m : ℤ, sc δ ≤ |a b - a b' - m|)
    (hall : ∀ b, ∀ p ∈ base, Avoids (a b) p) : B ≤ greedyBound base δ jf f := by
  rcases Nat.eq_zero_or_pos B with hB | hB
  · omega
  have hδR : 0 < sc δ := by
    have : sc 0 < sc δ := sc_lt_iff.mpr hδ
    simpa [sc] using this
  by_cases hb : base = []
  · simp only [greedyBound, hb, ite_true]
    let b0 : Fin B := ⟨0, hB⟩
    let a' : Fin B → ℝ := fun b => a b - a b0
    have hsep' : ∀ b b', b ≠ b' → ∀ m : ℤ, sc δ ≤ |a' b - a' b' - m| := by
      intro b b' h m; have := hsep b b' h m; simp only [a']; convert this using 2; ring
    obtain ⟨ys, hlen, hch, hlim, -⟩ := exists_chain a' hδR hsep' b0
    have ha0 : a' b0 = sc 0 := by simp [a', sc]
    rw [ha0] at hch hlim
    have := greedyAux_ge [] δ (S - δ) jf ys f 0 (by omega) (by simp) hch
      (by intro y hy; have := hlim y hy; rw [sc_sub, sc_S]; simp [sc] at this ⊢; linarith)
    omega
  · simp only [greedyBound, hb, ite_false]
    obtain ⟨τ, -, p0, hp0, b0, m, heq, hav⟩ := rotation base hb hB a hall
    let a' : Fin B → ℝ := fun b => a b - τ - m
    have hsep' : ∀ b b', b ≠ b' → ∀ m' : ℤ, sc δ ≤ |a' b - a' b' - m'| := by
      intro b b' h m'; have := hsep b b' h m'; simp only [a']; convert this using 2; ring
    have hav' : ∀ b, ∀ p ∈ base, Avoids (a' b) p := by
      intro b p hp
      have := (hav b p hp).shift (-m)
      simp only [a']; push_cast at this; convert this using 1; try ring
    obtain ⟨ys, hlen, hch, hlim, hys⟩ := exists_chain a' hδR hsep' b0
    have ha0 : a' b0 = sc p0.2 := by simp only [a']; rw [heq]; ring
    rw [ha0] at hch hlim
    have hA : ∀ y ∈ ys, ∀ p ∈ liftArcs base, ¬ ((sc p.1 < y) ∧ (y < sc p.2)) := by
      intro y hy
      obtain ⟨b, m', rfl⟩ := hys y hy
      exact avoids_lift (fun p hp => (hav' b p hp).shift m')
    have hg := greedyAux_ge (liftArcs base) δ (p0.2 + S - δ) jf ys f p0.2 (by omega) hA hch
      (by intro y hy; have := hlim y hy; rw [sc_sub, sc_add, sc_S]; linarith)
    have hnotin : insideAny (liftArcs base) p0.2 = false := by
      have hav0 : ∀ q ∈ liftArcs base, ¬ ((sc q.1 < sc p0.2) ∧ (sc p0.2 < sc q.2)) := by
        rw [← ha0]; exact avoids_lift (fun p hp => hav' b0 p hp)
      unfold insideAny
      rw [List.any_eq_false]
      intro q hq hc
      simp only [decide_eq_true_eq] at hc
      exact hav0 q hq ⟨sc_lt_iff.mpr hc.1, sc_lt_iff.mpr hc.2⟩
    have hle := le_foldr_max (l := (base.filter (fun p => !insideAny (liftArcs base) p.2)).map
      (fun p => 1 + greedyAux (liftArcs base) δ (p.2 + S - δ) jf f p.2))
      (x := 1 + greedyAux (liftArcs base) δ (p0.2 + S - δ) jf f p0.2)
      (List.mem_map.mpr ⟨p0, List.mem_filter.mpr ⟨hp0, by simp [hnotin]⟩, rfl⟩)
    omega

end CirclePacking

namespace CirclePacking

/-- **Greedy bound with a prescribed point.**  If a valid placement has a point in `[x1/S, x2/S]`
(modulo 1), then it has at most `greedyFromInterval base δ x1 x2 jf f` points. -/
theorem card_le_greedyFromInterval (base : List (ℤ × ℤ)) (δ x1 x2 : ℤ) (hδ : 0 < δ) (jf f : ℕ)
    {B : ℕ} (hBf : B ≤ f + 1) (a : Fin B → ℝ)
    (hsep : ∀ b b', b ≠ b' → ∀ m : ℤ, sc δ ≤ |a b - a b' - m|)
    (hall : ∀ b, ∀ p ∈ base, Avoids (a b) p)
    (b0 : Fin B) (m0 : ℤ) (h1 : sc x1 ≤ a b0 + m0) (h2 : a b0 + m0 ≤ sc x2) :
    B ≤ greedyFromInterval base δ x1 x2 jf f := by
  have hδR : 0 < sc δ := by
    have : sc 0 < sc δ := sc_lt_iff.mpr hδ
    simpa [sc] using this
  let a' : Fin B → ℝ := fun b => a b + m0
  have hsep' : ∀ b b', b ≠ b' → ∀ m : ℤ, sc δ ≤ |a' b - a' b' - m| := by
    intro b b' h m; have := hsep b b' h m; simp only [a']; convert this using 2; ring
  have hav' : ∀ b, ∀ p ∈ base, Avoids (a' b) p := fun b p hp => (hall b p hp).shift m0
  obtain ⟨ys, hlen, hch, hlim, hys⟩ := exists_chain a' hδR hsep' b0
  have hA : ∀ y ∈ ys, ∀ p ∈ liftArcs base, ¬ ((sc p.1 < y) ∧ (y < sc p.2)) := by
    intro y hy
    obtain ⟨b, m', rfl⟩ := hys y hy
    exact avoids_lift (fun p hp => (hav' b p hp).shift m')
  have hA0 : ∀ p ∈ liftArcs base, ¬ ((sc p.1 < a' b0) ∧ (a' b0 < sc p.2)) := by
    have := avoids_lift (fun p hp => (hav' b0 p hp).shift 0)
    simpa using this
  have hj : sc (jump (liftArcs base) jf x1) ≤ a' b0 := jump_le _ _ hA0 jf x1 h1
  have hg := greedyAux_ge (liftArcs base) δ (x2 + S - δ) jf ys f (jump (liftArcs base) jf x1)
    (by omega) hA (hch.mono hj)
    (by intro y hy; have := hlim y hy; rw [sc_sub, sc_add, sc_S]; simp only [a'] at this h2; linarith)
  unfold greedyFromInterval
  omega

end CirclePacking
