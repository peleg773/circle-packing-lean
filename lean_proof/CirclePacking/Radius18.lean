import CirclePacking.Radius17
import C18Compute

/-!
# Radius bounds for fewer than 18 circles

`RB18 m`: every packing of `m` unit circles has container parameter at least `sc (Ltab18 m)`.  For `m ≤ 13`
this is `RB17 m` (the tables agree); `m = 14` is a new branch-and-bound run (`ρ₁₄ > 3.31`); `15 ≤ m ≤ 17`
follow by restriction.
-/

open Real

namespace CirclePacking

def RB18 (m : ℕ) : Prop := ∀ (d : Fin m → ℂ) (r : ℝ), IsPacking d r → sc (Ltab18 m) ≤ r

lemma Ltab18_eq {m : ℕ} (hm : m ≤ 13) : Ltab18 m = Ltab17 m := by
  unfold Ltab18; rw [if_pos hm]

theorem rb18_14 (hchk : ∀ k ≤ 14, Certified (Prb14 k) (fun _ => false))
    (hprev : ∀ m', 0 < m' → m' < 14 → RB18 m') : RB18 14 :=
  rb_bnb_gen Ltab18 Prb14 (by norm_num) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun m' h0 hlt d r hd => hprev m' h0 hlt d r hd) (by decide) hchk

lemma rb18_restrict {m m' : ℕ} (h : m' ≤ m) (hL : Ltab18 m ≤ Ltab18 m') (hm' : RB18 m') : RB18 m :=
  fun d r hd => le_trans (sc_le_iff.mpr hL) (hm' _ r (hd.restrict h))

/-- all radius bounds needed for `n = 18` -/
theorem radiusBounds18
    (hrb : ∀ m, 8 ≤ m → m ≤ 11 → ∀ k ≤ m, Certified (Prb m k) (fun _ => false))
    (h12 : ∀ k ≤ 12, Certified (Prb12 k) (fun _ => false))
    (h13 : ∀ k ≤ 13, Certified (Prb13 k) (fun _ => false))
    (h14 : ∀ k ≤ 14, Certified (Prb14 k) (fun _ => false)) :
    RadiusBounds 18 (fun m => sc (Ltab18 m)) := by
  have h17 := radiusBounds17 hrb h12 h13
  have hsmall : ∀ m', 0 < m' → m' < 14 → RB18 m' := by
    intro m' h0 hlt d r hd
    rw [Ltab18_eq (by omega)]
    exact h17 m' h0 (by omega) d r hd
  have r14 : RB18 14 := rb18_14 h14 hsmall
  have r15 : RB18 15 := rb18_restrict (m' := 14) (by norm_num) (by decide) r14
  have r16 : RB18 16 := rb18_restrict (m' := 14) (by norm_num) (by decide) r14
  have r17 : RB18 17 := rb18_restrict (m' := 14) (by norm_num) (by decide) r14
  intro m h0 hlt d r hd
  by_cases hm : m < 14
  · exact hsmall m h0 hm d r hd
  · have : m = 14 ∨ m = 15 ∨ m = 16 ∨ m = 17 := by omega
    rcases this with rfl | rfl | rfl | rfl
    exacts [r14 d r hd, r15 d r hd, r16 d r hd, r17 d r hd]

end CirclePacking
