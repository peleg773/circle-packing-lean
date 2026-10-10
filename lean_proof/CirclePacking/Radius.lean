import CirclePacking.Canon

/-!
# Radius lower bounds for packings of fewer points

`RB m`: every packing of `m` unit circles has container parameter (centre radius) at least
`sc (Ltab m)`.  Proved for `m ≤ 2` directly, for `3 ≤ m ≤ 6` by pushing all centres onto the boundary
circle (the container parameter is `< 2`) and the greedy bound, for `8 ≤ m ≤ 11` by the branch and bound
(the certificates `Certified (Prb m k) _` are hypotheses here), and for `m = 7`, `12 ≤ m ≤ 14` by
restriction.
-/

open Real

namespace CirclePacking

lemma IsPacking.restrict {m m' : ℕ} (h : m' ≤ m) {d : Fin m → ℂ} {r : ℝ} (hd : IsPacking d r) :
    IsPacking (fun i : Fin m' => d (Fin.castLE h i)) r :=
  ⟨fun i => hd.1 _, fun i j hij => hd.2 _ _ (fun h' => hij (Fin.castLE_injective h h'))⟩

lemma IsPacking.mono {m : ℕ} {d : Fin m → ℂ} {r r' : ℝ} (hd : IsPacking d r) (h : r ≤ r') :
    IsPacking d r' :=
  ⟨fun i => le_trans (hd.1 i) h, hd.2⟩

/-- the radius bound for `m` points -/
def RB (m : ℕ) : Prop := ∀ (d : Fin m → ℂ) (r : ℝ), IsPacking d r → sc (Ltab m) ≤ r

lemma rb_restrict {m m' : ℕ} (h : m' ≤ m) (hL : Ltab m ≤ Ltab m') (hm' : RB m') : RB m :=
  fun d r hd => le_trans (sc_le_iff.mpr hL) (hm' _ r (hd.restrict h))

theorem rb1 : RB 1 := by
  intro d r hd
  have h0 : sc (Ltab 1) = 0 := by simp [Ltab, sc]
  rw [h0]
  exact le_trans (norm_nonneg _) (hd.1 0)

theorem rb2 : RB 2 := by
  intro d r hd
  have h := hd.2 0 1 (by decide)
  have h0 := hd.1 0
  have h1 := hd.1 1
  have h3 := norm_sub_le (d 0) (d 1)
  have e : sc (Ltab 2) = 1 := by
    have : Ltab 2 = S := rfl
    rw [this, sc_S]
  rw [e]; linarith

/-! ### `3 ≤ m ≤ 6`: all centres on the boundary -/

/-- in a container with parameter `r < 2` every centre can be pushed onto the boundary circle -/
lemma boundary_sep {m : ℕ} {d : Fin m → ℂ} {r : ℝ} (hd : IsPacking d r) (hr : r < 2)
    (i j : Fin m) (hij : i ≠ j) :
    4 ≤ 2 * r ^ 2 - 2 * r ^ 2 * Real.cos (2 * π * (toTurn (d i) - toTurn (d j))) := by
  obtain ⟨hn, hdd⟩ := hd
  have hr0 : 0 ≤ r := le_trans (norm_nonneg _) (hn i)
  have hpos : ∀ k l : Fin m, k ≠ l → 0 < ‖d k‖ := by
    intro k l hkl
    rcases (norm_nonneg (d k)).lt_or_eq with h | h
    · exact h
    · exfalso
      have hk0 : d k = 0 := norm_eq_zero.mp h.symm
      have := hdd k l hkl
      rw [hk0, zero_sub, norm_neg] at this
      linarith [hn l]
  have hpi := hpos i j hij
  have hpj := hpos j i (Ne.symm hij)
  have hsmall : ∀ k, r ^ 2 - 4 < ‖d k‖ ^ 2 := fun k => by nlinarith [norm_nonneg (d k)]
  have hpush : ∀ k, 0 < ‖d k‖ → ((r / ‖d k‖ : ℝ) : ℂ) * d k = polar r (toTurn (d k)) := by
    intro k hk
    have hz : polar ‖d k‖ (toTurn (d k)) = d k := polar_toTurn (d k)
    calc ((r / ‖d k‖ : ℝ) : ℂ) * d k = ((r / ‖d k‖ : ℝ) : ℂ) * polar ‖d k‖ (toTurn (d k)) := by rw [hz]
      _ = polar r (toTurn (d k)) := by
        apply Complex.ext <;>
          simp only [polar, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] <;>
          field_simp <;> ring
  have h1 : 2 ≤ ‖((r / ‖d i‖ : ℝ) : ℂ) * d i - d j‖ := pushout_pair (hsmall i) (hn i) (hn j) (hdd i j hij)
  have hni : ‖((r / ‖d i‖ : ℝ) : ℂ) * d i‖ ≤ r := by rw [norm_pushed hpi hr0]
  have h2 := pushout_pair (hsmall j) (hn j) hni (by rw [norm_sub_rev]; exact h1)
  rw [hpush i hpi, hpush j hpj] at h2
  have := dist_sq_of_polar rfl rfl h2
  have e : Real.cos (2 * π * (toTurn (d j) - toTurn (d i))) =
      Real.cos (2 * π * (toTurn (d i) - toTurn (d j))) := by
    rw [← Real.cos_neg]; ring_nf
  rw [e] at this
  nlinarith

/-- the integer facts behind the bound for `3 ≤ m ≤ 6` -/
def smallOK (m : ℕ) : Bool :=
  decide (0 < Ltab m) && decide (0 < smallDelta m) && decide (2 * smallDelta m ≤ S) &&
  decide ((Ltab m * Ltab m - 2 * S * S) * S ≤ cosZ (smallDelta m) * (Ltab m * Ltab m)) &&
  decide (Ltab m < 2 * S) && decide (greedyBound [] (smallDelta m) 60 (m - 1) < m)

theorem rb_small {m : ℕ} (hm : 1 ≤ m) (hc : smallOK m = true) : RB m := by
  unfold smallOK at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨hρ, hδ⟩, hδ2⟩, hδc⟩, h2⟩, hg⟩ := hc
  intro d r hd
  by_contra hlt
  push Not at hlt
  have h2' : sc (Ltab m) < 2 := by
    have := sc_lt_iff.mpr h2
    rwa [show (2 : ℤ) * S = S + S by ring, sc_add, sc_S, show (1 : ℝ) + 1 = 2 by norm_num] at this
  have hr2 : r < 2 := lt_trans hlt h2'
  have hsep : ∀ b b' : Fin m, b ≠ b' → ∀ k : ℤ,
      sc (smallDelta m) ≤ |toTurn (d b) - toTurn (d b') - k| := by
    intro b b' hbb k
    apply sep_of_cos hρ hδ.le hδ2 hδc _ k
    have h := boundary_sep hd hr2 b b' hbb
    have hc1 := Real.cos_le_one (2 * π * (toTurn (d b) - toTurn (d b')))
    have hr0 : 0 ≤ r := le_trans (norm_nonneg _) (hd.1 b)
    have : r ^ 2 ≤ sc (Ltab m) ^ 2 := by nlinarith
    nlinarith
  have := card_le_greedyBound [] (smallDelta m) hδ 60 (m - 1) (by omega) (fun b => toTurn (d b)) hsep
    (by simp)
  omega

theorem smallOK3 : smallOK 3 = true := by decide +kernel
theorem smallOK4 : smallOK 4 = true := by decide +kernel
theorem smallOK5 : smallOK 5 = true := by decide +kernel
theorem smallOK6 : smallOK 6 = true := by decide +kernel

theorem rb3 : RB 3 := rb_small (by norm_num) smallOK3
theorem rb4 : RB 4 := rb_small (by norm_num) smallOK4
theorem rb5 : RB 5 := rb_small (by norm_num) smallOK5
theorem rb6 : RB 6 := rb_small (by norm_num) smallOK6
theorem rb7 : RB 7 := rb_restrict (m' := 6) (by norm_num) (le_of_eq rfl) rb6

/-! ### `8 ≤ m ≤ 11`: branch and bound -/

theorem rb_bnb {m : ℕ} (hm : 1 ≤ m) (hprev : ∀ m', 0 < m' → m' < m → RB m')
    (hρ2 : 2 * S < Ltab m) (hρeq : PrbRho m = Ltab m)
    (hchk : ∀ k ≤ m, Certified (Prb m k) (fun _ => false)) : RB m := by
  intro d r hd
  by_contra hlt
  push Not at hlt
  set L := sc (Ltab m) with hLdef
  have hL2 : 2 < L := by
    have := sc_lt_iff.mpr hρ2
    rwa [show (2 : ℤ) * S = S + S by ring, sc_add, sc_S, show (1 : ℝ) + 1 = 2 by norm_num] at this
  set ρ' := max r ((2 + L) / 2) with hρ'def
  have hρ'2 : 2 < ρ' := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hρ'L : ρ' ≤ L := max_le hlt.le (by linarith)
  have hd' := hd.mono (le_max_left r ((2 + L) / 2))
  obtain ⟨hpk, hIB, -⟩ := pushOut_spec hρ'2 hd'
  have hRB : RadiusBounds m (fun m' => sc (Ltab m')) :=
    fun m' h0 hlt' d' r' hd'' => hprev m' h0 hlt' d' r' hd''
  obtain ⟨k, hk, s, ψ, a, hA⟩ := exists_canonical (by omega) hρ'2 hRB _ hpk hIB
  have hρP : ρ' ≤ sc (Prb m k).ρ := by
    show ρ' ≤ sc (PrbRho m); rw [hρeq]; exact hρ'L
  have hAd := AdmR.toAdm (P := Prb m k) rfl rfl hρ'2.le hρP hA
  obtain ⟨b, hb, -⟩ := (hchk k hk).2 _ _ _ hAd
  exact absurd hb (by simp)

end CirclePacking
