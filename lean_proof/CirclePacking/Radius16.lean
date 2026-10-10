import CirclePacking.Radius
import C16Compute

/-!
# Radius bounds for fewer than 16 circles

`RB16 m`: every packing of `m` unit circles has container parameter at least `sc (Ltab16 m)`.  For `m ≤ 11`
this is `RB m` (the tables agree); `m = 12` is a new branch-and-bound run; `13 ≤ m ≤ 15` follow by
restriction.
-/

open Real

namespace CirclePacking

def RB16 (m : ℕ) : Prop := ∀ (d : Fin m → ℂ) (r : ℝ), IsPacking d r → sc (Ltab16 m) ≤ r

lemma Ltab16_eq {m : ℕ} (hm : m ≤ 11) : Ltab16 m = Ltab m := by
  interval_cases m <;> rfl

lemma rb16_of_rb {m : ℕ} (hm : m ≤ 11) (h : RB m) : RB16 m := by
  intro d r hd; rw [Ltab16_eq hm]; exact h d r hd

/-- the branch-and-bound argument for a radius bound, for any table and parameter family -/
theorem rb_bnb_gen {m : ℕ} (L : ℕ → ℤ) (P : ℕ → Params) (hm : 1 ≤ m)
    (hPn : ∀ k, (P k).n = m) (hPk : ∀ k, (P k).k = k) (hPL : ∀ k, (P k).L = L) (hPρ : ∀ k, (P k).ρ = L m)
    (hprev : ∀ m', 0 < m' → m' < m → ∀ (d : Fin m' → ℂ) (r : ℝ), IsPacking d r → sc (L m') ≤ r)
    (hρ2 : 2 * S < L m) (hchk : ∀ k ≤ m, Certified (P k) (fun _ => false)) :
    ∀ (d : Fin m → ℂ) (r : ℝ), IsPacking d r → sc (L m) ≤ r := by
  intro d r hd
  by_contra hlt
  push Not at hlt
  set Lm := sc (L m) with hLdef
  have hL2 : 2 < Lm := by
    have := sc_lt_iff.mpr hρ2
    rwa [show (2 : ℤ) * S = S + S by ring, sc_add, sc_S, show (1 : ℝ) + 1 = 2 by norm_num] at this
  set ρ' := max r ((2 + Lm) / 2) with hρ'def
  have hρ'2 : 2 < ρ' := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hρ'L : ρ' ≤ Lm := max_le hlt.le (by linarith)
  have hd' := hd.mono (le_max_left r ((2 + Lm) / 2))
  obtain ⟨hpk, hIB, -⟩ := pushOut_spec hρ'2 hd'
  have hRB : RadiusBounds m (fun m' => sc (L m')) :=
    fun m' h0 hlt' d' r' hd'' => hprev m' h0 hlt' d' r' hd''
  obtain ⟨k, hk, s, ψ, a, hA⟩ := exists_canonical (by omega) hρ'2 hRB _ hpk hIB
  have hρP : ρ' ≤ sc (P k).ρ := by rw [hPρ]; exact hρ'L
  have hA' : AdmR m k ρ' (fun m' => sc ((P k).L m')) s ψ a := by rw [hPL]; exact hA
  have hAd := AdmR.toAdm (P := P k) (hPn k) (hPk k) hρ'2.le hρP hA'
  obtain ⟨b, hb, -⟩ := (hchk k hk).2 _ _ _ hAd
  exact absurd hb (by simp)

theorem rb16_12 (hchk : ∀ k ≤ 12, Certified (Prb12 k) (fun _ => false))
    (hprev : ∀ m', 0 < m' → m' < 12 → RB16 m') : RB16 12 :=
  rb_bnb_gen Ltab16 Prb12 (by norm_num) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun m' h0 hlt d r hd => hprev m' h0 hlt d r hd) (by decide) hchk

lemma rb16_restrict {m m' : ℕ} (h : m' ≤ m) (hL : Ltab16 m ≤ Ltab16 m') (hm' : RB16 m') : RB16 m :=
  fun d r hd => le_trans (sc_le_iff.mpr hL) (hm' _ r (hd.restrict h))

/-- all radius bounds needed for `n = 16` -/
theorem radiusBounds16
    (hrb : ∀ m, 8 ≤ m → m ≤ 11 → ∀ k ≤ m, Certified (Prb m k) (fun _ => false))
    (h12 : ∀ k ≤ 12, Certified (Prb12 k) (fun _ => false)) :
    RadiusBounds 16 (fun m => sc (Ltab16 m)) := by
  have r8 : RB 8 := rb_bnb (by norm_num)
    (fun m' h0 hlt => by
      interval_cases m'
      exacts [rb1, rb2, rb3, rb4, rb5, rb6, rb7])
    (by decide) rfl (hrb 8 le_rfl (by norm_num))
  have r9 : RB 9 := rb_bnb (by norm_num)
    (fun m' h0 hlt => by
      interval_cases m'
      exacts [rb1, rb2, rb3, rb4, rb5, rb6, rb7, r8])
    (by decide) rfl (hrb 9 (by norm_num) (by norm_num))
  have r10 : RB 10 := rb_bnb (by norm_num)
    (fun m' h0 hlt => by
      interval_cases m'
      exacts [rb1, rb2, rb3, rb4, rb5, rb6, rb7, r8, r9])
    (by decide) rfl (hrb 10 (by norm_num) (by norm_num))
  have r11 : RB 11 := rb_bnb (by norm_num)
    (fun m' h0 hlt => by
      interval_cases m'
      exacts [rb1, rb2, rb3, rb4, rb5, rb6, rb7, r8, r9, r10])
    (by decide) rfl (hrb 11 (by norm_num) le_rfl)
  have hsmall : ∀ m', 0 < m' → m' < 12 → RB16 m' := by
    intro m' h0 hlt
    interval_cases m'
    exacts [rb16_of_rb (by norm_num) rb1, rb16_of_rb (by norm_num) rb2, rb16_of_rb (by norm_num) rb3,
      rb16_of_rb (by norm_num) rb4, rb16_of_rb (by norm_num) rb5, rb16_of_rb (by norm_num) rb6,
      rb16_of_rb (by norm_num) rb7, rb16_of_rb (by norm_num) r8, rb16_of_rb (by norm_num) r9,
      rb16_of_rb (by norm_num) r10, rb16_of_rb (by norm_num) r11]
  have r12 : RB16 12 := rb16_12 h12 hsmall
  have r13 : RB16 13 := rb16_restrict (m' := 12) (by norm_num) (le_of_eq rfl) r12
  have r14 : RB16 14 := rb16_restrict (m' := 12) (by norm_num) (le_of_eq rfl) r12
  have r15 : RB16 15 := rb16_restrict (m' := 12) (by norm_num) (le_of_eq rfl) r12
  intro m h0 hlt d r hd
  interval_cases m
  · exact hsmall 1 (by norm_num) (by norm_num) d r hd
  · exact hsmall 2 (by norm_num) (by norm_num) d r hd
  · exact hsmall 3 (by norm_num) (by norm_num) d r hd
  · exact hsmall 4 (by norm_num) (by norm_num) d r hd
  · exact hsmall 5 (by norm_num) (by norm_num) d r hd
  · exact hsmall 6 (by norm_num) (by norm_num) d r hd
  · exact hsmall 7 (by norm_num) (by norm_num) d r hd
  · exact hsmall 8 (by norm_num) (by norm_num) d r hd
  · exact hsmall 9 (by norm_num) (by norm_num) d r hd
  · exact hsmall 10 (by norm_num) (by norm_num) d r hd
  · exact hsmall 11 (by norm_num) (by norm_num) d r hd
  · exact r12 d r hd
  · exact r13 d r hd
  · exact r14 d r hd
  · exact r15 d r hd

end CirclePacking
