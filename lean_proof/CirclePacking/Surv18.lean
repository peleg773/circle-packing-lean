import CirclePacking.Surv
import C18Surv

/-!
# Survivors of 18 circles: assigning boundary circles to windows

`surv_assign_gen`: `K` boundary circles and `K` windows (each narrower than the angular separation `δ`), whose
gaps are blocked (covered by a forbidden arc, or excluded by the greedy count): the circles lie one per window.
This is `surv_assign17` (`Surv17.lean`) for any number of windows.
-/

open Real Finset

namespace CirclePacking

lemma sc_wStartG_K (win : ℕ → ℤ × ℤ) (K : ℕ) : sc (wStartG win K K) = sc (win 0).1 + 1 := by
  simp [wStartG, sc_add, sc_S]

lemma wStartG_lt (win : ℕ → ℤ × ℤ) {K w : ℕ} (hw : w < K) : wStartG win K w = (win w).1 := by
  simp [wStartG, show w ≠ K by omega]

/-- **Assignment of `K` boundary points to `K` windows.** -/
theorem surv_assign_gen {K : ℕ} (hK : 0 < K) (win : ℕ → ℤ × ℤ) {δ : ℤ} {jf : ℕ} {arcs : List (ℤ × ℤ)}
    (hδ : 0 < δ)
    (hbad : ∀ w < K, ((liftArcs arcs).any
        (fun q => decide (q.1 < (badIG win K w).1 ∧ (badIG win K w).2 < q.2)) ||
      decide (greedyFromInterval arcs δ (badIG win K w).1 (badIG win K w).2 jf (K - 1) < K)) = true)
    (hwid : ∀ w < K, (win w).2 - (win w).1 < δ)
    (a : Fin K → ℝ)
    (hsep : ∀ b b', b ≠ b' → ∀ m : ℤ, sc δ ≤ |a b - a b' - m|)
    (hall : ∀ b, ∀ p ∈ arcs, Avoids (a b) p) :
    ∃ σ : Fin K → Fin K, Function.Injective σ ∧ ∀ w : Fin K, ∃ m : ℤ,
      sc (win w).1 ≤ a (σ w) + m ∧ a (σ w) + m ≤ sc (win w).2 := by
  have hin : ∀ b : Fin K, ∃ w : Fin K, ∃ m : ℤ,
      sc (win w).1 ≤ a b + m ∧ a b + m ≤ sc (win w).2 := by
    intro b
    set L := sc (win 0).1
    set m : ℤ := ⌈L - a b⌉
    have hm1 : L ≤ a b + m := by have := Int.le_ceil (L - a b); linarith
    have hm2 : a b + m ≤ L + 1 := by have := Int.ceil_lt_add_one (L - a b); linarith
    have h0 : sc (wStartG win K 0) ≤ a b + m := by rw [wStartG_lt win hK]; exact hm1
    have h11 : a b + m ≤ sc (wStartG win K (K - 1 + 1)) := by
      rw [show K - 1 + 1 = K by omega, sc_wStartG_K]; exact hm2
    obtain ⟨w, hw, hw1, hw2⟩ := exists_window (fun w => sc (wStartG win K w)) (K - 1) h0 h11
    rw [wStartG_lt win (by omega)] at hw1
    by_cases hx : a b + m ≤ sc (win w).2
    · exact ⟨⟨w, by omega⟩, m, hw1, hx⟩
    · exfalso
      have hx' : sc (badIG win K w).1 ≤ a b + m := by simp only [badIG]; linarith
      have hx'' : a b + m ≤ sc (badIG win K w).2 := by simp only [badIG]; exact hw2
      have hb := hbad w (by omega)
      simp only [Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq] at hb
      rcases hb with ⟨q, hq, hq1, hq2⟩ | hg
      · have hav : ∀ p ∈ arcs, Avoids (a b + m) p := fun p hp => (hall b p hp).shift m
        exact avoids_lift hav q hq ⟨lt_of_lt_of_le (sc_lt_iff.mpr hq1) hx',
          lt_of_le_of_lt hx'' (sc_lt_iff.mpr hq2)⟩
      · have := card_le_greedyFromInterval arcs δ (badIG win K w).1 (badIG win K w).2 hδ jf (K - 1)
          (by omega) a hsep hall b m hx' hx''
        omega
  choose wf mf hwf using hin
  have hinj : Function.Injective wf := by
    intro b b' heq
    by_contra hne
    have h1 := hwf b
    have h2 := hwf b'
    rw [heq] at h1
    have hw := hwid (wf b') (wf b').isLt
    have hwR : sc (win (wf b')).2 - sc (win (wf b')).1 < sc δ := by
      rw [← sc_sub]; exact sc_lt_iff.mpr hw
    have hs := hsep b b' hne (mf b' - mf b)
    push_cast at hs
    have : |a b - a b' - (mf b' - mf b)| < sc δ := by
      rw [abs_lt]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    linarith
  have hbij : Function.Bijective wf := Finite.injective_iff_bijective.mp hinj
  set e := Equiv.ofBijective wf hbij
  refine ⟨e.symm, e.symm.injective, ?_⟩
  intro w
  have h := hwf (e.symm w)
  have he : wf (e.symm w) = w := e.apply_symm_apply w
  rw [he] at h
  exact ⟨_, h⟩

end CirclePacking
