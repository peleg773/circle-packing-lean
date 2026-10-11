import CirclePacking.Surv18

/-!
# Survivors of 18 circles: the hexagon windows (capacity two)

`surv_assign_hex`: eleven boundary circles and six windows narrower than `2δ` whose gaps are covered by forbidden
arcs.  Exactly one window (`m0`) is short of a circle, every other window holds two, pinned near its ends: the
left one in `[l, r - δ]`, the right one in `[l + δ, r]`.  `τ` assigns the ten boundary slots of the hexagon core
with short window `m0`.
-/

open Real Finset

namespace CirclePacking

/-- three points pairwise at least `d` apart do not fit in an interval shorter than `2d` -/
lemma not_three_in {l r d x y z : ℝ} (hd : 2 * d > r - l) (hx : l ≤ x ∧ x ≤ r) (hy : l ≤ y ∧ y ≤ r)
    (hz : l ≤ z ∧ z ≤ r) (hxy : d ≤ |x - y|) (hxz : d ≤ |x - z|) (hyz : d ≤ |y - z|) : False := by
  rcases le_total x y with h1 | h1 <;> rcases le_total y z with h2 | h2 <;> rcases le_total x z with h3 | h3
  all_goals
    first
    | (rw [abs_of_nonpos (by linarith : x - y ≤ 0)] at hxy) | (rw [abs_of_nonneg (by linarith : 0 ≤ x - y)] at hxy)
  all_goals
    first
    | (rw [abs_of_nonpos (by linarith : x - z ≤ 0)] at hxz) | (rw [abs_of_nonneg (by linarith : 0 ≤ x - z)] at hxz)
  all_goals
    first
    | (rw [abs_of_nonpos (by linarith : y - z ≤ 0)] at hyz) | (rw [abs_of_nonneg (by linarith : 0 ≤ y - z)] at hyz)
  all_goals linarith [hx.1, hx.2, hy.1, hy.2, hz.1, hz.2]

lemma hexWin_ne {m0 i : ℕ} : hexWin m0 i ≠ m0 := by
  unfold hexWin; split_ifs <;> omega

lemma hexWin_lt {m0 i : ℕ} (_hm : m0 < 6) (hi : i < 5) : hexWin m0 i < 6 := by
  unfold hexWin; split_ifs <;> omega

lemma hexWin_inj {m0 i j : ℕ} (h : hexWin m0 i = hexWin m0 j) : i = j := by
  unfold hexWin at h; split_ifs at h <;> omega

lemma hex_sum_ten : ∀ m0 w : Fin 6, w ≠ m0 → (∑ v : Fin 6, if v = m0 ∨ v = w then 1 else 2) = 10 := by
  decide

/-- **Assignment for the hexagon.** -/
theorem surv_assign_hex (win : ℕ → ℤ × ℤ) {δ : ℤ} {arcs : List (ℤ × ℤ)} (hδ : 0 < δ)
    (hgap : ∀ w < 6, (liftArcs arcs).any
        (fun q => decide (q.1 < (badIG win 6 w).1 ∧ (badIG win 6 w).2 < q.2)) = true)
    (hwid : ∀ w < 6, (win w).2 - (win w).1 < 2 * δ)
    (a : Fin 11 → ℝ)
    (hsep : ∀ b b', b ≠ b' → ∀ m : ℤ, sc δ ≤ |a b - a b' - m|)
    (hall : ∀ b, ∀ p ∈ arcs, Avoids (a b) p) :
    ∃ m0 : Fin 6, ∃ τ : Fin 10 → Fin 11, Function.Injective τ ∧ ∀ s : Fin 10, ∃ m : ℤ,
      sc (hexSlotLo win δ m0 s) ≤ a (τ s) + m ∧ a (τ s) + m ≤ sc (hexSlotHi win δ m0 s) := by
  -- every point lies in a window
  have hin : ∀ b : Fin 11, ∃ w : Fin 6, ∃ m : ℤ, sc (win w).1 ≤ a b + m ∧ a b + m ≤ sc (win w).2 := by
    intro b
    set L := sc (win 0).1
    set m : ℤ := ⌈L - a b⌉
    have hm1 : L ≤ a b + m := by have := Int.le_ceil (L - a b); linarith
    have hm2 : a b + m ≤ L + 1 := by have := Int.ceil_lt_add_one (L - a b); linarith
    have h0 : sc (wStartG win 6 0) ≤ a b + m := by rw [wStartG_lt win (by norm_num)]; exact hm1
    have h11 : a b + m ≤ sc (wStartG win 6 (5 + 1)) := by rw [sc_wStartG_K]; exact hm2
    obtain ⟨w, hw, hw1, hw2⟩ := exists_window (fun w => sc (wStartG win 6 w)) 5 h0 h11
    rw [wStartG_lt win (by omega)] at hw1
    by_cases hx : a b + m ≤ sc (win w).2
    · exact ⟨⟨w, by omega⟩, m, hw1, hx⟩
    · exfalso
      have hx' : sc (badIG win 6 w).1 ≤ a b + m := by simp only [badIG]; linarith
      have hx'' : a b + m ≤ sc (badIG win 6 w).2 := by simp only [badIG]; exact hw2
      have hb := hgap w (by omega)
      simp only [List.any_eq_true, decide_eq_true_eq] at hb
      obtain ⟨q, hq, hq1, hq2⟩ := hb
      have hav : ∀ p ∈ arcs, Avoids (a b + m) p := fun p hp => (hall b p hp).shift m
      exact avoids_lift hav q hq ⟨lt_of_lt_of_le (sc_lt_iff.mpr hq1) hx',
        lt_of_le_of_lt hx'' (sc_lt_iff.mpr hq2)⟩
  choose wf mf hwf using hin
  set x : Fin 11 → ℝ := fun b => a b + mf b with hx
  have hxw : ∀ b, sc (win (wf b)).1 ≤ x b ∧ x b ≤ sc (win (wf b)).2 := fun b => hwf b
  have hxsep : ∀ b b', b ≠ b' → sc δ ≤ |x b - x b'| := by
    intro b b' hne
    have := hsep b b' hne (mf b' - mf b)
    simp only [hx]; push_cast at this ⊢
    have e : a b + mf b - (a b' + mf b') = a b - a b' - (mf b' - mf b) := by ring
    rw [e]; exact this
  have hwidR : ∀ w : Fin 6, 2 * sc δ > sc (win w).2 - sc (win w).1 := by
    intro w
    have h := hwid w w.isLt
    have : sc ((win w).2 - (win w).1) < sc (2 * δ) := sc_lt_iff.mpr h
    rw [sc_sub] at this
    have e : sc (2 * δ) = 2 * sc δ := by simp [sc]; ring
    linarith
  -- fibres
  set F : Fin 6 → Finset (Fin 11) := fun w => Finset.univ.filter (fun b => wf b = w) with hF
  have hFle : ∀ w, (F w).card ≤ 2 := by
    intro w
    by_contra hc
    push Not at hc
    obtain ⟨b1, b2, b3, h1, h2, h3, h12, h13, h23⟩ := Finset.two_lt_card_iff.mp hc
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2 h3
    have e1 := hxw b1
    have e2 := hxw b2
    have e3 := hxw b3
    rw [h1] at e1
    rw [h2] at e2
    rw [h3] at e3
    exact not_three_in (hwidR w) e1 e2 e3 (hxsep _ _ h12) (hxsep _ _ h13) (hxsep _ _ h23)
  have hsum : ∑ w, (F w).card = 11 := by
    have := Finset.card_eq_sum_card_fiberwise (f := wf) (s := Finset.univ) (t := Finset.univ)
      (fun b _ => Finset.mem_univ _)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    exact this.symm
  -- the short window
  have hm0 : ∃ m0, (F m0).card < 2 := by
    by_contra h
    push Not at h
    have : ∑ w, (F w).card = 12 := by
      have hall2 : ∀ w, (F w).card = 2 := fun w => le_antisymm (hFle w) (h w)
      simp [hall2]
    omega
  obtain ⟨m0, hm0⟩ := hm0
  have hfull : ∀ w, w ≠ m0 → (F w).card = 2 := by
    intro w hw
    by_contra h
    have hw1 : (F w).card ≤ 1 := by have := hFle w; omega
    have hle : ∑ v, (F v).card ≤ ∑ v : Fin 6, (if v = m0 ∨ v = w then 1 else 2) := by
      apply Finset.sum_le_sum
      intro v _
      by_cases h1 : v = m0
      · subst h1; simp; omega
      · by_cases h2 : v = w
        · subst h2; simp [h1]; omega
        · simp [h1, h2]; exact hFle v
    have hval := hex_sum_ten m0 w hw
    omega
  -- the two points of a full window, ordered
  have hpair : ∀ w, w ≠ m0 → ∃ bl br : Fin 11, wf bl = w ∧ wf br = w ∧ bl ≠ br ∧ x bl + sc δ ≤ x br := by
    intro w hw
    obtain ⟨b, b', hbb', hF2⟩ := Finset.card_eq_two.mp (hfull w hw)
    have hb : b ∈ F w := by rw [hF2]; simp
    have hb' : b' ∈ F w := by rw [hF2]; simp
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hb hb'
    have hs := hxsep b b' hbb'
    rcases le_total (x b) (x b') with h | h
    · rw [abs_of_nonpos (by linarith)] at hs
      exact ⟨b, b', hb, hb', hbb', by linarith⟩
    · rw [abs_of_nonneg (by linarith)] at hs
      exact ⟨b', b, hb', hb, hbb'.symm, by linarith⟩
  choose! bl br hbl hbr hblr hord using hpair
  let wOf : Fin 10 → Fin 6 := fun s => ⟨hexWin m0 (s / 2), hexWin_lt m0.isLt (by omega)⟩
  have hwne : ∀ s, wOf s ≠ m0 := fun s h => hexWin_ne (congrArg Fin.val h)
  let τ : Fin 10 → Fin 11 := fun s => if s.val % 2 = 0 then bl (wOf s) else br (wOf s)
  have key : ∀ s, wf (τ s) = wOf s := by
    intro s
    show wf (if s.val % 2 = 0 then bl (wOf s) else br (wOf s)) = wOf s
    split_ifs
    · exact hbl _ (hwne s)
    · exact hbr _ (hwne s)
  refine ⟨m0, τ, ?_, ?_⟩
  · intro s t hst
    have hw : (s : ℕ) / 2 = (t : ℕ) / 2 := by
      have := congrArg (fun b => (wf b).val) hst
      simp only [key] at this
      exact hexWin_inj this
    have hwst : wOf s = wOf t := by
      apply Fin.ext; show hexWin m0 (s / 2) = hexWin m0 (t / 2); rw [hw]
    apply Fin.ext
    have hst' : (if s.val % 2 = 0 then bl (wOf s) else br (wOf s)) =
        (if t.val % 2 = 0 then bl (wOf t) else br (wOf t)) := hst
    rw [hwst] at hst'
    split_ifs at hst' with h1 h2 h2
    · omega
    · exact absurd hst' (hblr _ (hwne t))
    · exact absurd hst'.symm (hblr _ (hwne t))
    · omega
  · intro s
    have hw0 := hwne s
    have hl := hxw (bl (wOf s))
    have hr := hxw (br (wOf s))
    rw [hbl _ hw0] at hl
    rw [hbr _ hw0] at hr
    have ho := hord _ hw0
    show ∃ m : ℤ, sc (hexSlotLo win δ m0 s) ≤ a (if s.val % 2 = 0 then bl (wOf s) else br (wOf s)) + m ∧
      a (if s.val % 2 = 0 then bl (wOf s) else br (wOf s)) + m ≤ sc (hexSlotHi win δ m0 s)
    simp only [hexSlotLo, hexSlotHi]
    split_ifs with h
    · refine ⟨mf (bl (wOf s)), hl.1, ?_⟩
      rw [sc_sub]
      have : x (bl (wOf s)) ≤ sc (win (wOf s)).2 - sc δ := by linarith [hr.2]
      exact this
    · refine ⟨mf (br (wOf s)), ?_, hr.2⟩
      rw [sc_add]
      have : sc (win (wOf s)).1 + sc δ ≤ x (br (wOf s)) := by linarith [hl.1]
      exact this

end CirclePacking
