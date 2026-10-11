import CirclePacking.Radius16
import C17Compute

/-!
# Radius bounds for fewer than 17 circles

`RB17 m`: every packing of `m` unit circles has container parameter at least `sc (Ltab17 m)`.  For `m ≤ 12`
this is `RB16 m` (the tables agree); `m = 13` is a new branch-and-bound run; `14 ≤ m ≤ 16` follow by
restriction.
-/

open Real

namespace CirclePacking

def RB17 (m : ℕ) : Prop := ∀ (d : Fin m → ℂ) (r : ℝ), IsPacking d r → sc (Ltab17 m) ≤ r

lemma Ltab17_eq {m : ℕ} (hm : m ≤ 12) : Ltab17 m = Ltab16 m := by
  unfold Ltab17; rw [if_pos hm]

theorem rb17_13 (hchk : ∀ k ≤ 13, Certified (Prb13 k) (fun _ => false))
    (hprev : ∀ m', 0 < m' → m' < 13 → RB17 m') : RB17 13 :=
  rb_bnb_gen Ltab17 Prb13 (by norm_num) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun m' h0 hlt d r hd => hprev m' h0 hlt d r hd) (by decide) hchk

lemma rb17_restrict {m m' : ℕ} (h : m' ≤ m) (hL : Ltab17 m ≤ Ltab17 m') (hm' : RB17 m') : RB17 m :=
  fun d r hd => le_trans (sc_le_iff.mpr hL) (hm' _ r (hd.restrict h))

/-- all radius bounds for fewer than 17 circles (used for `n = 18`) -/
theorem radiusBounds17
    (hrb : ∀ m, 8 ≤ m → m ≤ 11 → ∀ k ≤ m, Certified (Prb m k) (fun _ => false))
    (h12 : ∀ k ≤ 12, Certified (Prb12 k) (fun _ => false))
    (h13 : ∀ k ≤ 13, Certified (Prb13 k) (fun _ => false)) :
    RadiusBounds 17 (fun m => sc (Ltab17 m)) := by
  have h16 := radiusBounds16 hrb h12
  have hsmall : ∀ m', 0 < m' → m' < 13 → RB17 m' := by
    intro m' h0 hlt d r hd
    rw [Ltab17_eq (by omega)]
    exact h16 m' h0 (by omega) d r hd
  have r13 : RB17 13 := rb17_13 h13 hsmall
  have r14 : RB17 14 := rb17_restrict (m' := 13) (by norm_num) (by decide) r13
  have r15 : RB17 15 := rb17_restrict (m' := 13) (by norm_num) (by decide) r13
  have r16 : RB17 16 := rb17_restrict (m' := 13) (by norm_num) (by decide) r13
  intro m h0 hlt d r hd
  by_cases hm : m < 13
  · exact hsmall m h0 hm d r hd
  · have : m = 13 ∨ m = 14 ∨ m = 15 ∨ m = 16 := by omega
    rcases this with rfl | rfl | rfl | rfl
    exacts [r13 d r hd, r14 d r hd, r15 d r hd, r16 d r hd]

end CirclePacking
