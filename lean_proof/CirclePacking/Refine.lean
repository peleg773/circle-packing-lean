import CirclePacking.Chunks2
import C17Ref

/-!
# Refinement of survivors, and monotonicity of the branch and bound

* `bnb_mono`, `checkPath_mono`: a computation that succeeds with a survivor test `surv` also succeeds with any
  weaker test `surv'` (one accepting every box `surv` accepts).
* `certified_of_survRef`: if a run is certified with the refined test `survRef P' surv fuel`, where `P'` is the
  run's parameters with another box tolerance, it is certified with `surv` itself: a box accepted by the finer
  branch and bound contains only configurations lying in boxes accepted by `surv` (`bnb_sound` for `P'`).
-/

namespace CirclePacking

/-- the branch and bound is monotone in the survivor test -/
theorem bnb_mono {P : Params} {surv surv' : List IBox → Bool} (hs : ∀ b, surv b = true → surv' b = true) :
    ∀ (f : ℕ) (bx : List IBox), bnb P surv f bx = true → bnb P surv' f bx = true
  | 0, _, h => by simp [bnb] at h
  | f + 1, bx, h => by
    simp only [bnb] at h ⊢
    cases hp : propagate P P.rounds bx with
    | none => rfl
    | some b =>
      rw [hp] at h
      simp only at h ⊢
      by_cases hc : capTest P b = true
      · simp [hc]
      · by_cases hw : wide P b = true
        · rcases hsb : splitBox b with ⟨b1, b2⟩
          simp only [hc, hw, hsb, ite_true, Bool.false_eq_true, ite_false, Bool.and_eq_true] at h ⊢
          exact ⟨bnb_mono hs f _ h.1, bnb_mono hs f _ h.2⟩
        · simp only [hc, hw, Bool.false_eq_true, ite_false] at h ⊢
          exact hs b h

/-- a chunk-tree path computation is monotone in the survivor test -/
theorem checkPath_mono {P : Params} {surv surv' : List IBox → Bool} (hs : ∀ b, surv b = true → surv' b = true)
    {fuel : ℕ} : ∀ (p : List (ℕ × ℕ × ℕ)) (b : List IBox), checkPath P surv fuel p b = true →
      checkPath P surv' fuel p b = true
  | [], b, h => bnb_mono hs fuel b h
  | (d, m, i) :: rest, b, h => by
    simp only [checkPath, List.all_eq_true] at h ⊢
    exact fun x hx => checkPath_mono hs rest x (h x hx)

/-- `survRef` accepts every box that `surv` accepts -/
theorem survRef_of_surv {P' : Params} {surv : List IBox → Bool} {fuel : ℕ} {b : List IBox}
    (h : surv b = true) : survRef P' surv fuel b = true := by
  simp [survRef, h]

/-- admissibility does not depend on the box tolerance -/
theorem Adm.withTol {P : Params} {t : ℤ} {s ψ : ℕ → ℝ} {a : Fin (P.n - P.k) → ℝ} (hA : Adm P s ψ a) :
    Adm { P with tol := t } s ψ a :=
  ⟨hA.s_nonneg, hA.s_sq, hA.ii, hA.ib, hA.bb, hA.ψ01, hA.smax, hA.ψ0, hA.ord, hA.refl, hA.rb⟩

/-- soundness of the refined survivor test -/
theorem survRef_sound {P : Params} {t : ℤ} (hP' : paramsOK { P with tol := t } = true)
    {surv : List IBox → Bool} {fuel : ℕ} {bx : List IBox} (h : survRef { P with tol := t } surv fuel bx = true)
    {s ψ : ℕ → ℝ} {a : Fin (P.n - P.k) → ℝ} (hA : Adm P s ψ a) (hF : Fits P bx s ψ) :
    ∃ b, surv b = true ∧ Fits P b s ψ := by
  unfold survRef at h
  rcases Bool.or_eq_true_iff.mp h with h1 | h2
  · exact ⟨bx, h1, hF⟩
  · exact bnb_sound hP' surv fuel bx h2 s ψ a hA.withTol hF

/-- **Refinement is sound**: certification with the refined test gives certification with `surv` -/
theorem certified_of_survRef {P : Params} {t : ℤ} (hP' : paramsOK { P with tol := t } = true)
    {surv : List IBox → Bool} {fuel : ℕ} (h : Certified P (survRef { P with tol := t } surv fuel)) :
    Certified P surv := by
  refine ⟨h.1, fun s ψ a hA => ?_⟩
  obtain ⟨b, hb, hF⟩ := h.2 s ψ a hA
  exact survRef_sound hP' hb hA hF

end CirclePacking
