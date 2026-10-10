import CirclePacking.Box

/-!
# Soundness of the branch-and-bound checker (`C15Compute.bnb`)

Canonical form (angle ordered):
* interior point `0` has maximal radius and angle `0`;
* the angles of points `1 .. k-1` are non-decreasing (in turns, in `[0,1]`);
* reflection: `ψ 1 + ψ (k-1) ≤ 1` when `k ≥ 3`.
-/

open Real

namespace CirclePacking

/-- An admissible canonical configuration: interior radii `s`, angles `ψ` (turns), boundary angles
`a` (turns), all constraints at container parameter `sc P.ρ`. -/
structure Adm (P : Params) (s ψ : ℕ → ℝ) (a : Fin (P.n - P.k) → ℝ) : Prop where
  s_nonneg : ∀ j < P.k, 0 ≤ s j
  s_sq : ∀ j < P.k, s j ^ 2 ≤ sc P.ρ ^ 2 - 4
  ii : ∀ i < P.k, ∀ j < P.k, i ≠ j →
    4 ≤ s i ^ 2 + s j ^ 2 - 2 * s i * s j * Real.cos (2 * π * (ψ i - ψ j))
  ib : ∀ b, ∀ j < P.k,
    4 ≤ sc P.ρ ^ 2 + s j ^ 2 - 2 * sc P.ρ * s j * Real.cos (2 * π * (a b - ψ j))
  bb : ∀ b b', b ≠ b' →
    4 ≤ 2 * sc P.ρ ^ 2 - 2 * sc P.ρ ^ 2 * Real.cos (2 * π * (a b - a b'))
  ψ01 : ∀ j < P.k, 0 ≤ ψ j ∧ ψ j ≤ 1
  smax : ∀ j < P.k, s j ≤ s 0
  ψ0 : 0 < P.k → ψ 0 = 0
  ord : ∀ j, 1 ≤ j → j + 1 < P.k → ψ j ≤ ψ (j + 1)
  refl : 3 ≤ P.k → ψ 1 + ψ (P.k - 1) ≤ 1
  rb : ∀ T : Finset ℕ, (∀ i ∈ T, i < P.k) → 0 < T.card → T.card < P.n →
    ∃ i ∈ T, sc (P.L T.card) ≤ s i

/-- `(s, ψ)` lies in the box list -/
def InBox (bx : List IBox) (s ψ : ℕ → ℝ) : Prop := ∀ j < bx.length, InI (gI bx j) (s j) (ψ j)

/-- the box list has the right length and contains the configuration -/
def Fits (P : Params) (bx : List IBox) (s ψ : ℕ → ℝ) : Prop := bx.length = P.k ∧ InBox bx s ψ

@[simp] lemma length_mapI (bx : List IBox) (f : ℕ → IBox → IBox) : (mapI bx f).length = bx.length := by
  simp [mapI]

lemma gI_mapI (bx : List IBox) (f : ℕ → IBox → IBox) {j : ℕ} (hj : j < bx.length) :
    gI (mapI bx f) j = f j (gI bx j) := by
  simp [mapI, gI, List.getD_eq_getElem?_getD, hj]

lemma InBox_mapI {bx : List IBox} {f : ℕ → IBox → IBox} {s ψ : ℕ → ℝ}
    (h : ∀ j < bx.length, InI (gI bx j) (s j) (ψ j) → InI (f j (gI bx j)) (s j) (ψ j))
    (hb : InBox bx s ψ) : InBox (mapI bx f) s ψ := by
  intro j hj
  rw [length_mapI] at hj
  rw [gI_mapI bx f hj]
  exact h j hj (hb j hj)

lemma gI_eq_getElem {bx : List IBox} {i : ℕ} (hi : i < bx.length) : gI bx i = bx[i] := by
  simp [gI, List.getD_eq_getElem?_getD, hi]

/-! ### Parameters -/

lemma paramsOK_facts {P : Params} (hP : paramsOK P = true) :
    0 < P.ρ ∧ 0 ≤ P.Rhi ∧ P.ρ * P.ρ - 4 * S * S ≤ P.Rhi * P.Rhi ∧ 0 < P.δ ∧ 2 * P.δ ≤ S ∧
      (P.ρ * P.ρ - 2 * S * S) * S ≤ cosZ P.δ * (P.ρ * P.ρ) := by
  unfold paramsOK at hP
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hP
  exact ⟨h1, h2, h3, h4, h5, h6⟩

lemma s_le_Rhi {P : Params} (hP : paramsOK P = true) {s ψ : ℕ → ℝ} {a : Fin (P.n - P.k) → ℝ}
    (hA : Adm P s ψ a) {j : ℕ} (hj : j < P.k) : s j ≤ sc P.Rhi := by
  obtain ⟨-, hR0, hR2, -⟩ := paramsOK_facts hP
  have hR0' := sc_nonneg hR0
  have hR2' : sc P.ρ ^ 2 - 4 ≤ sc P.Rhi ^ 2 := by
    have h' : ((P.ρ * P.ρ - 4 * S * S : ℤ) : ℝ) ≤ ((P.Rhi * P.Rhi : ℤ) : ℝ) := by exact_mod_cast hR2
    push_cast at h'
    have hS := S_pos
    unfold sc
    have e1 : ((P.ρ : ℝ) / S) ^ 2 - 4 = ((P.ρ : ℝ) * P.ρ - 4 * S * S) / (S * S) := by field_simp
    have e2 : ((P.Rhi : ℝ) / S) ^ 2 = ((P.Rhi : ℝ) * P.Rhi) / (S * S) := by field_simp
    rw [e1, e2]
    exact div_le_div_of_nonneg_right h' (by positivity)
  have h1 := hA.s_sq j hj
  have h2 := hA.s_nonneg j hj
  nlinarith

/-! ### Step A -/

lemma foldl_max_slo_le {x : ℝ} (hx : 0 ≤ x) :
    ∀ (l : List IBox) (acc : ℤ), sc acc ≤ x → (∀ I ∈ l, sc I.slo ≤ x) →
      sc (l.foldl (fun acc I => max acc I.slo) acc) ≤ x
  | [], acc, h, _ => by simpa using h
  | I :: l, acc, h, hl => by
    simp only [List.foldl_cons]
    apply foldl_max_slo_le hx l
    · rcases le_total acc I.slo with hle | hle
      · rw [max_eq_right hle]; exact hl I (by simp)
      · rw [max_eq_left hle]; exact h
    · intro J hJ; exact hl J (by simp [hJ])

lemma sc_max_le {x y : ℤ} {r : ℝ} (hx : sc x ≤ r) (hy : sc y ≤ r) : sc (max x y) ≤ r := by
  rcases le_total x y with h | h
  · rw [max_eq_right h]; exact hy
  · rw [max_eq_left h]; exact hx

lemma le_sc_min {x y : ℤ} {r : ℝ} (hx : r ≤ sc x) (hy : r ≤ sc y) : r ≤ sc (min x y) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h]; exact hx
  · rw [min_eq_right h]; exact hy

lemma stepA_sound {P : Params} (hP : paramsOK P = true) {s ψ : ℕ → ℝ} {a : Fin (P.n - P.k) → ℝ}
    (hA : Adm P s ψ a) {bx : List IBox} (hF : Fits P bx s ψ) : Fits P (stepA P bx) s ψ := by
  obtain ⟨hlen, hin⟩ := hF
  refine ⟨by simp [stepA, hlen], ?_⟩
  unfold stepA
  apply InBox_mapI _ hin
  intro j hj hI
  obtain ⟨h1, h2, h3, h4⟩ := hI
  have hjk : j < P.k := hlen ▸ hj
  have hk0 : 0 < P.k := lt_of_le_of_lt (Nat.zero_le _) hjk
  have hsmax := hA.smax j hjk
  have hRhi := s_le_Rhi hP hA hjk
  have h0box := hin 0 (hlen ▸ hk0)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- slo
    show sc (aSlo P bx j (gI bx j)) ≤ s j
    unfold aSlo
    by_cases hj0 : j = 0
    · subst hj0
      rw [if_pos rfl]
      refine sc_max_le (sc_max_le h1 ?_) ?_
      · apply foldl_max_slo_le (hA.s_nonneg 0 hk0) bx 0 (by rw [sc_zero]; exact hA.s_nonneg 0 hk0)
        intro I hIm
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hIm
        have hik : i < P.k := hlen ▸ hi
        have := (hin i hi).1
        rw [gI_eq_getElem hi] at this
        exact le_trans this (hA.smax i hik)
      · by_cases hkn : bx.length < P.n
        · rw [if_pos hkn]
          have hT : ∀ i ∈ Finset.range P.k, i < P.k := fun i hi => Finset.mem_range.mp hi
          rw [hlen] at hkn ⊢
          obtain ⟨i, hi, hLi⟩ := hA.rb (Finset.range P.k) hT (by simp [hk0]) (by simpa using hkn)
          rw [Finset.card_range] at hLi
          exact le_trans hLi (hA.smax i (Finset.mem_range.mp hi))
        · rw [if_neg hkn, sc_zero]; exact hA.s_nonneg 0 hk0
    · rw [if_neg hj0]; exact h1
  · -- shi
    show s j ≤ sc (aShi P bx j (gI bx j))
    unfold aShi
    split_ifs with hj0
    · exact le_sc_min h2 hRhi
    · exact le_sc_min (le_sc_min h2 hRhi) (le_trans hsmax h0box.2.1)
  · -- plo
    show sc (aPlo bx j (gI bx j)) ≤ ψ j
    unfold aPlo
    split_ifs with hj2
    · refine sc_max_le h3 ?_
      have hj1 : j - 1 < bx.length := by omega
      have := (hin (j - 1) hj1).2.2.1
      have hord := hA.ord (j - 1) (by omega) (by omega)
      have e : j - 1 + 1 = j := by omega
      rw [e] at hord
      exact le_trans this hord
    · exact h3
  · -- phi
    show ψ j ≤ sc (aPhi3 bx j (aPhi2 bx j (aPhi1 bx j (gI bx j))))
    have hphi1 : ψ j ≤ sc (aPhi1 bx j (gI bx j)) := by
      unfold aPhi1
      split_ifs with hc
      · refine le_sc_min h4 ?_
        have := (hin (j + 1) (by omega)).2.2.2
        exact le_trans (hA.ord j hc.1 (by omega)) this
      · exact h4
    have hphi2 : ψ j ≤ sc (aPhi2 bx j (aPhi1 bx j (gI bx j))) := by
      unfold aPhi2
      split_ifs with hc
      · refine le_sc_min hphi1 ?_
        obtain ⟨hk3, hj1⟩ := hc
        subst hj1
        have hl := (hin (bx.length - 1) (by omega)).2.2.1
        have hr := hA.refl (hlen ▸ hk3)
        rw [← hlen] at hr
        rw [sc_sub, sc_S]
        linarith
      · exact hphi1
    unfold aPhi3
    split_ifs with hc
    · refine le_sc_min hphi2 ?_
      obtain ⟨hk3, hjl⟩ := hc
      have hl := (hin 1 (by omega)).2.2.1
      have hr := hA.refl (hlen ▸ hk3)
      rw [← hlen, ← hjl] at hr
      rw [sc_sub, sc_S]
      linarith
    · exact hphi2

/-! ### Step B: counting rule -/

lemma mem_belowL {bx : List IBox} {r : ℤ} {i : ℕ} :
    i ∈ belowL bx r ↔ i < bx.length ∧ (gI bx i).shi < r := by
  simp [belowL, List.mem_filter, List.mem_range]

lemma belowL_nodup (bx : List IBox) (r : ℤ) : (belowL bx r).Nodup :=
  (List.nodup_range).filter _

lemma card_belowL (bx : List IBox) (r : ℤ) : (belowL bx r).toFinset.card = (belowL bx r).length :=
  List.toFinset_card_of_nodup (belowL_nodup bx r)

lemma countPrune_sound {P : Params} {s ψ : ℕ → ℝ} {a : Fin (P.n - P.k) → ℝ}
    (hA : Adm P s ψ a) {bx : List IBox} (hF : Fits P bx s ψ) : countPrune P bx = false := by
  obtain ⟨hlen, hin⟩ := hF
  by_contra hc
  simp only [countPrune, Bool.not_eq_false, List.any_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at hc
  obtain ⟨m, -, ⟨⟨hm2, hmn⟩, hmc⟩⟩ := hc
  rw [← card_belowL] at hmc
  obtain ⟨T, hT, hTcard⟩ := Finset.exists_subset_card_eq hmc
  have hTk : ∀ i ∈ T, i < P.k := by
    intro i hi
    have := List.mem_toFinset.mp (hT hi)
    rw [mem_belowL] at this
    omega
  obtain ⟨i, hiT, hi⟩ := hA.rb T hTk (by omega) (by omega)
  have hib := List.mem_toFinset.mp (hT hiT)
  rw [mem_belowL] at hib
  have h1 := (hin i hib.1).2.1
  have h2 : sc (gI bx i).shi < sc (P.L m) := sc_lt_iff.mpr hib.2
  rw [hTcard] at hi
  linarith

lemma raiseSlo_le {P : Params} {s ψ : ℕ → ℝ} {a : Fin (P.n - P.k) → ℝ}
    (hA : Adm P s ψ a) {bx : List IBox} (hF : Fits P bx s ψ) {j : ℕ} (hj : j < bx.length) :
    ∀ (ms : List ℕ) (x : ℤ), sc x ≤ s j →
      sc (ms.foldl (fun acc m =>
        if 2 ≤ m ∧ m < P.n ∧ (belowL bx (P.L m)).length + 1 = m ∧ j ∉ belowL bx (P.L m)
        then max acc (P.L m) else acc) x) ≤ s j
  | [], x, hx => by simpa using hx
  | m :: ms, x, hx => by
    obtain ⟨hlen, hin⟩ := hF
    simp only [List.foldl_cons]
    apply raiseSlo_le hA ⟨hlen, hin⟩ hj ms
    split_ifs with hc
    · obtain ⟨hm2, hmn, hcard, hjn⟩ := hc
      refine sc_max_le hx ?_
      set T := (belowL bx (P.L m)).toFinset
      have hjT : j ∉ T := by simpa [T] using hjn
      have hTk : ∀ i ∈ insert j T, i < P.k := by
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · omega
        · have := List.mem_toFinset.mp hi
          rw [mem_belowL] at this; omega
      have hcardS : (insert j T).card = m := by
        rw [Finset.card_insert_of_notMem hjT, card_belowL]; omega
      obtain ⟨i, hiS, hi⟩ := hA.rb (insert j T) hTk (by omega) (by omega)
      rw [hcardS] at hi
      rcases Finset.mem_insert.mp hiS with rfl | hiT
      · exact hi
      · exfalso
        have := List.mem_toFinset.mp hiT
        rw [mem_belowL] at this
        have h1 := (hin i this.1).2.1
        have h2 : sc (gI bx i).shi < sc (P.L m) := sc_lt_iff.mpr this.2
        linarith
    · exact hx

lemma countRaise_sound {P : Params} {s ψ : ℕ → ℝ} {a : Fin (P.n - P.k) → ℝ}
    (hA : Adm P s ψ a) {bx : List IBox} (hF : Fits P bx s ψ) : Fits P (countRaise P bx) s ψ := by
  obtain ⟨hlen, hin⟩ := hF
  refine ⟨by simp [countRaise, hlen], ?_⟩
  unfold countRaise
  apply InBox_mapI _ hin
  intro j hj hI
  obtain ⟨h1, h2, h3, h4⟩ := hI
  exact ⟨raiseSlo_le hA ⟨hlen, hin⟩ hj _ _ h1, h2, h3, h4⟩

/-! ### Step C: pair conflicts -/

lemma pairPrune_sound {P : Params} {s ψ : ℕ → ℝ} {a : Fin (P.n - P.k) → ℝ}
    (hA : Adm P s ψ a) {bx : List IBox} (hF : Fits P bx s ψ) : pairPrune bx = false := by
  obtain ⟨hlen, hin⟩ := hF
  by_contra hc
  simp only [pairPrune, Bool.not_eq_false, List.any_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at hc
  obtain ⟨i, hi, j, hj, ⟨hij, -⟩, ht⟩ := hc
  have hik : i < P.k := hlen ▸ hi
  have hjk : j < P.k := hlen ▸ hj
  have h := pairTest_sound ht (hin i hi) (hin j hj) (hA.ψ01 i hik) (hA.ψ01 j hjk)
  have h2 := hA.ii i hik j hjk (by omega)
  linarith

/-! ### Step D: angular and radial contraction -/

lemma angStepG_sound {I J : IBox} (pm : ℤ) (go : Bool) {si ψi sj ψj : ℝ} (hI : InI I si ψi)
    (hJ : InI J sj ψj) (hd : 4 ≤ si ^ 2 + sj ^ 2 - 2 * si * sj * Real.cos (2 * π * (ψi - ψj))) :
    InI (angStepG I J pm go) sj ψj := by
  unfold angStepG
  split_ifs with hg hc
  · simp only [Bool.and_eq_true] at hc
    have hav := pm_avoids hc.2 hI hJ hd
    obtain ⟨h1, h2, h3, h4⟩ := hJ
    exact ⟨h1, h2, shrinkLo_le hav h3, le_shrinkHi hav h4⟩
  · exact hJ
  · exact hJ

lemma angStep_sound {I J : IBox} {fI fJ : QBox} {si ψi sj ψj : ℝ} (hI : InI I si ψi)
    (hJ : InI J sj ψj) (hd : 4 ≤ si ^ 2 + sj ^ 2 - 2 * si * sj * Real.cos (2 * π * (ψi - ψj))) :
    InI (angStep I J fI fJ) sj ψj :=
  angStepG_sound _ _ hI hJ hd

lemma radialOK_sound {I : IBox} {c u v : ℤ} (h : radialOK I c u v = true) {si ψi sj ψj : ℝ}
    (hI : InI I si ψi) (hc : sc c ≤ Real.cos (2 * π * (ψj - ψi))) (hu : sc u ≤ sj)
    (hv : sj ≤ sc v) : sj ^ 2 + si ^ 2 - 2 * sj * si * Real.cos (2 * π * (ψj - ψi)) < 4 := by
  unfold radialOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hI0, hu0⟩, -⟩, hlt⟩ := h
  obtain ⟨h1, h2, -, -⟩ := hI
  have hQ := corners_quad (I := ⟨u, v, 0, 0⟩) (J := I) hlt (x := sj) (y := si) hu hv h1 h2
  have hsj : 0 ≤ sj := le_trans (sc_nonneg hu0) hu
  have hsi : 0 ≤ si := le_trans (sc_nonneg hI0) h1
  have hprod : 0 ≤ sj * si := mul_nonneg hsj hsi
  nlinarith [mul_le_mul_of_nonneg_left hc hprod]

lemma radStepG_sound {I J : IBox} (g : Option (Int64 × Int64)) {si ψi sj ψj : ℝ} (hI : InI I si ψi)
    (hJ : InI J sj ψj) (hψi : 0 ≤ ψi ∧ ψi ≤ 1) (hψj : 0 ≤ ψj ∧ ψj ≤ 1)
    (hd : 4 ≤ sj ^ 2 + si ^ 2 - 2 * sj * si * Real.cos (2 * π * (ψj - ψi))) :
    InI (radStepG I J g) sj ψj := by
  unfold radStepG
  rcases g with _ | ⟨uf, vf⟩
  · exact hJ
  simp only
  split_ifs with hr
  · obtain ⟨h1, h2, h3, h4⟩ := hJ
    have hc : sc (cosLB J I) ≤ Real.cos (2 * π * (ψj - ψi)) :=
      cosLB_spec J I h3 h4 hI.2.2.1 hI.2.2.2 hψj hψi
    have hnot : ¬ (sc (fromQ uf + 1) ≤ sj ∧ sj ≤ sc (fromQ vf)) := by
      intro huv
      have := radialOK_sound hr hI hc huv.1 huv.2
      linarith
    refine ⟨?_, ?_, h3, h4⟩
    · unfold shrinkSlo
      split_ifs with hc2
      · have hu : sc (fromQ uf + 1) ≤ sc J.slo := sc_le_iff.mpr hc2.1
        by_contra hlt; push Not at hlt
        exact hnot ⟨by linarith, hlt.le⟩
      · exact h1
    · unfold shrinkShi
      split_ifs with hc2
      · have hv : sc J.shi ≤ sc (fromQ vf) := sc_le_iff.mpr hc2.2
        by_contra hlt; push Not at hlt
        exact hnot ⟨hlt.le, by linarith⟩
      · exact h2
  · exact hJ

lemma radStep_sound {I J : IBox} {fI fJ : QBox} {si ψi sj ψj : ℝ} (hI : InI I si ψi)
    (hJ : InI J sj ψj) (hψi : 0 ≤ ψi ∧ ψi ≤ 1) (hψj : 0 ≤ ψj ∧ ψj ≤ 1)
    (hd : 4 ≤ sj ^ 2 + si ^ 2 - 2 * sj * si * Real.cos (2 * π * (ψj - ψi))) :
    InI (radStep I J fI fJ) sj ψj :=
  radStepG_sound _ hI hJ hψi hψj hd

lemma contract_fold {P : Params} {s ψ : ℕ → ℝ} {a : Fin (P.n - P.k) → ℝ}
    (hA : Adm P s ψ a) {bx : List IBox} (hF : Fits P bx s ψ) (fb : List QBox) {j : ℕ}
    (hj : j < bx.length) :
    ∀ (is : List ℕ) (J : IBox), (∀ i ∈ is, i < bx.length) → InI J (s j) (ψ j) →
      InI (is.foldl (fun J' i => if i = j then J' else contractPair (gI bx i) J' (fb.getD i default))
        J) (s j) (ψ j)
  | [], J, _, hJ => by simpa using hJ
  | i :: is, J, his, hJ => by
    obtain ⟨hlen, hin⟩ := hF
    simp only [List.foldl_cons]
    apply contract_fold hA ⟨hlen, hin⟩ fb hj is _ (fun i' h' => his i' (by simp [h']))
    split_ifs with hij
    · exact hJ
    · have hi : i < bx.length := his i (by simp)
      have hik : i < P.k := hlen ▸ hi
      have hjk : j < P.k := hlen ▸ hj
      have hd := hA.ii i hik j hjk hij
      unfold contractPair
      dsimp only
      have h1 := angStep_sound (fI := fb.getD i default) (fJ := toQB J) (hin i hi) hJ hd
      exact radStep_sound (hin i hi) h1 (hA.ψ01 i hik) (hA.ψ01 j hjk) (hA.ii j hjk i hik (Ne.symm hij))

lemma contract_sound {P : Params} {s ψ : ℕ → ℝ} {a : Fin (P.n - P.k) → ℝ}
    (hA : Adm P s ψ a) {bx : List IBox} (hF : Fits P bx s ψ) : Fits P (contract bx) s ψ := by
  obtain ⟨hlen, hin⟩ := hF
  refine ⟨by simp [contract, hlen], ?_⟩
  unfold contract
  dsimp only
  apply InBox_mapI _ hin
  intro j hj hI
  exact contract_fold hA ⟨hlen, hin⟩ _ hj _ _ (fun i hi => List.mem_range.mp hi) hI

/-! ### Step E: emptiness; rounds -/

lemma nonemptyB_sound {P : Params} {s ψ : ℕ → ℝ} {bx : List IBox} (hF : Fits P bx s ψ) :
    nonemptyB bx = true := by
  obtain ⟨hlen, hin⟩ := hF
  simp only [nonemptyB, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  intro I hI
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hI
  have h := hin i hi
  rw [gI_eq_getElem hi] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨sc_le_iff.mp (le_trans h1 h2), sc_le_iff.mp (le_trans h3 h4)⟩

lemma round1_sound {P : Params} (hP : paramsOK P = true) {s ψ : ℕ → ℝ} {a : Fin (P.n - P.k) → ℝ}
    (hA : Adm P s ψ a) {bx : List IBox} (hF : Fits P bx s ψ) :
    ∃ b, round1 P bx = some b ∧ Fits P b s ψ := by
  have h1 := stepA_sound hP hA hF
  have hc := countPrune_sound hA h1
  have h2 := countRaise_sound hA h1
  have hp := pairPrune_sound hA h2
  have h3 := contract_sound hA h2
  have hn := nonemptyB_sound h3
  refine ⟨contract (countRaise P (stepA P bx)), ?_, h3⟩
  simp [round1, hc, hp, hn]

lemma propagate_sound {P : Params} (hP : paramsOK P = true) {s ψ : ℕ → ℝ} {a : Fin (P.n - P.k) → ℝ}
    (hA : Adm P s ψ a) : ∀ (r : ℕ) {bx : List IBox}, Fits P bx s ψ →
      ∃ b, propagate P r bx = some b ∧ Fits P b s ψ
  | 0, bx, hF => ⟨bx, rfl, hF⟩
  | r + 1, bx, hF => by
    obtain ⟨b, hb, hFb⟩ := round1_sound hP hA hF
    simp only [propagate, hb]
    split_ifs with heq
    · exact ⟨b, rfl, hFb⟩
    · exact propagate_sound hP hA r hFb

/-! ### Capacity test -/

lemma capTest_sound {P : Params} (hP : paramsOK P = true) {s ψ : ℕ → ℝ} {a : Fin (P.n - P.k) → ℝ}
    (hA : Adm P s ψ a) {bx : List IBox} (hF : Fits P bx s ψ) : capTest P bx = false := by
  obtain ⟨hlen, hin⟩ := hF
  obtain ⟨hρ, -, -, hδ0, hδ1, hδc⟩ := paramsOK_facts hP
  by_contra hc
  simp only [capTest, Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq] at hc
  have hlt := hc.2
  have hsep : ∀ b b', b ≠ b' → ∀ m : ℤ, sc P.δ ≤ |a b - a b' - m| :=
    fun b b' hbb m => sep_of_cos hρ hδ0.le hδ1 hδc (hA.bb b b' hbb) m
  have hall : ∀ b, ∀ p ∈ arcsOf P bx, Avoids (a b) p := by
    intro b p hp
    simp only [arcsOf, List.mem_filterMap] at hp
    obtain ⟨I, hI, hIp⟩ := hp
    split_ifs at hIp with hok
    · simp only [Option.some.injEq] at hIp
      subst hIp
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hI
      have hjk : j < P.k := hlen ▸ hj
      have hin' := hin j hj
      rw [gI_eq_getElem hj] at hin'
      exact arc_avoids hok hρ hin' (hA.s_sq j hjk) (hA.ib b j hjk)
  have := card_le_greedyBound (arcsOf P bx) P.δ hδ0 P.jf (P.n - P.k - 1) (by omega) a hsep hall
  omega

/-! ### Splitting -/

lemma gI_set (bx : List IBox) (j : ℕ) (v : IBox) (i : ℕ) (hj : j < bx.length) :
    gI (bx.set j v) i = if i = j then v else gI bx i := by
  unfold gI
  by_cases hij : i = j
  · subst hij; simp [List.getD_eq_getElem?_getD, hj]
  · simp [List.getD_eq_getElem?_getD, hij, Ne.symm hij]

lemma fits_set {P : Params} {s ψ : ℕ → ℝ} {bx : List IBox} (hF : Fits P bx s ψ) {j : ℕ} {v : IBox}
    (hv : j < bx.length → InI v (s j) (ψ j)) : Fits P (bx.set j v) s ψ := by
  obtain ⟨hlen, hin⟩ := hF
  refine ⟨by simp [hlen], ?_⟩
  intro i hi
  rw [List.length_set] at hi
  by_cases hj : j < bx.length
  · rw [gI_set bx j v i hj]
    split_ifs with hij
    · subst hij; exact hv hj
    · exact hin i hi
  · rw [List.set_eq_of_length_le (by omega)]
    exact hin i hi

lemma splitBox_sound {P : Params} {s ψ : ℕ → ℝ} {bx : List IBox} (hF : Fits P bx s ψ) :
    Fits P (splitBox bx).1 s ψ ∨ Fits P (splitBox bx).2 s ψ := by
  unfold splitBox
  dsimp only
  set j := (chooseSplit bx).1
  split_ifs with hc
  · by_cases hm : s j ≤ sc (((gI bx j).slo + (gI bx j).shi) / 2)
    · left
      exact fits_set hF (fun hj => by
        obtain ⟨h1, h2, h3, h4⟩ := hF.2 j hj
        exact ⟨h1, hm, h3, h4⟩)
    · right
      push Not at hm
      exact fits_set hF (fun hj => by
        obtain ⟨h1, h2, h3, h4⟩ := hF.2 j hj
        exact ⟨hm.le, h2, h3, h4⟩)
  · by_cases hm : ψ j ≤ sc (((gI bx j).plo + (gI bx j).phi) / 2)
    · left
      exact fits_set hF (fun hj => by
        obtain ⟨h1, h2, h3, h4⟩ := hF.2 j hj
        exact ⟨h1, h2, h3, hm⟩)
    · right
      push Not at hm
      exact fits_set hF (fun hj => by
        obtain ⟨h1, h2, h3, h4⟩ := hF.2 j hj
        exact ⟨h1, h2, hm.le, h4⟩)

/-! ### The recursion -/

theorem bnb_sound {P : Params} (hP : paramsOK P = true) (surv : List IBox → Bool) :
    ∀ (f : ℕ) (bx : List IBox), bnb P surv f bx = true →
      ∀ (s ψ : ℕ → ℝ) (a : Fin (P.n - P.k) → ℝ), Adm P s ψ a → Fits P bx s ψ →
        ∃ b, surv b = true ∧ Fits P b s ψ
  | 0, _, h, _, _, _, _, _ => by simp [bnb] at h
  | f + 1, bx, h, s, ψ, a, hA, hF => by
    obtain ⟨b, hb, hFb⟩ := propagate_sound hP hA P.rounds hF
    have hcap := capTest_sound hP hA hFb
    simp only [bnb, hb, hcap, Bool.false_eq_true, ite_false] at h
    by_cases hw : wide P b = true
    · simp only [hw, ite_true, Bool.and_eq_true] at h
      rcases splitBox_sound hFb with h1 | h2
      · exact bnb_sound hP surv f _ h.1 s ψ a hA h1
      · exact bnb_sound hP surv f _ h.2 s ψ a hA h2
    · simp only [Bool.not_eq_true] at hw
      simp only [hw, Bool.false_eq_true, ite_false] at h
      exact ⟨b, h, hFb⟩

lemma root_fits {P : Params} (hP : paramsOK P = true) {s ψ : ℕ → ℝ} {a : Fin (P.n - P.k) → ℝ}
    (hA : Adm P s ψ a) : Fits P (rootBox P) s ψ := by
  refine ⟨by simp [rootBox], ?_⟩
  intro j hj
  simp only [rootBox, List.length_map, List.length_range] at hj
  have hRhi := s_le_Rhi hP hA hj
  have hs0 := hA.s_nonneg j hj
  have hψ := hA.ψ01 j hj
  simp only [gI, rootBox, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some]
  split_ifs with hj0
  · subst hj0
    have := hA.ψ0 hj
    refine ⟨by rw [sc_zero]; exact hs0, hRhi, by rw [sc_zero, this], by rw [sc_zero, this]⟩
  · exact ⟨by rw [sc_zero]; exact hs0, hRhi, by rw [sc_zero]; exact hψ.1, by rw [sc_S]; exact hψ.2⟩

theorem checkRun_sound {P : Params} {surv : List IBox → Bool} {fuel : ℕ}
    (h : checkRun P surv fuel = true) {s ψ : ℕ → ℝ} {a : Fin (P.n - P.k) → ℝ} (hA : Adm P s ψ a) :
    ∃ b, surv b = true ∧ Fits P b s ψ := by
  simp only [checkRun, Bool.and_eq_true] at h
  exact bnb_sound h.1 surv fuel _ h.2 s ψ a hA (root_fits h.1 hA)

/-! ### Chunked runs -/

theorem frontier_sound {P : Params} (hP : paramsOK P = true) {s ψ : ℕ → ℝ} {a : Fin (P.n - P.k) → ℝ}
    (hA : Adm P s ψ a) : ∀ (d : ℕ) (bx : List IBox), Fits P bx s ψ →
      ∃ b ∈ frontier P d bx, Fits P b s ψ
  | 0, bx, hF => ⟨bx, by simp [frontier], hF⟩
  | d + 1, bx, hF => by
    obtain ⟨b, hb, hFb⟩ := propagate_sound hP hA P.rounds hF
    have hcap := capTest_sound hP hA hFb
    by_cases hw : wide P b = true
    · rcases splitBox_sound hFb with h1 | h2
      · obtain ⟨c, hc, hFc⟩ := frontier_sound hP hA d _ h1
        refine ⟨c, ?_, hFc⟩
        simp only [frontier, hb, hcap, hw, Bool.false_eq_true, ite_false, ite_true]
        exact List.mem_append_left _ hc
      · obtain ⟨c, hc, hFc⟩ := frontier_sound hP hA d _ h2
        refine ⟨c, ?_, hFc⟩
        simp only [frontier, hb, hcap, hw, Bool.false_eq_true, ite_false, ite_true]
        exact List.mem_append_right _ hc
    · simp only [Bool.not_eq_true] at hw
      refine ⟨b, ?_, hFb⟩
      simp [frontier, hb, hcap, hw]

lemma mem_chunkAux {α : Type} {m : ℕ} (hm : 0 < m) {x : α} :
    ∀ (l : List α) (pos : ℕ), x ∈ l → ∃ i < m, x ∈ chunkAux m i pos l
  | [], _, h => by simp at h
  | y :: l, pos, h => by
    rcases List.mem_cons.mp h with rfl | h'
    · refine ⟨chunkKey pos % m, Nat.mod_lt _ hm, ?_⟩
      simp [chunkAux]
    · obtain ⟨i, hi, hx⟩ := mem_chunkAux hm l (pos + 1) h'
      refine ⟨i, hi, ?_⟩
      unfold chunkAux
      split_ifs
      · exact List.mem_cons_of_mem _ hx
      · exact hx

/-- `surv` is a complete certificate for the run `P`: every admissible configuration lies in a box
accepted by `surv` -/
def Certified (P : Params) (surv : List IBox → Bool) : Prop :=
  paramsOK P = true ∧ ∀ (s ψ : ℕ → ℝ) (a : Fin (P.n - P.k) → ℝ), Adm P s ψ a →
    ∃ b, surv b = true ∧ Fits P b s ψ

theorem certified_of_checkRun {P : Params} {surv : List IBox → Bool} {fuel : ℕ}
    (h : checkRun P surv fuel = true) : Certified P surv := by
  refine ⟨?_, fun s ψ a hA => checkRun_sound h hA⟩
  simp only [checkRun, Bool.and_eq_true] at h
  exact h.1

theorem certified_of_chunks {P : Params} {surv : List IBox → Bool} {fuel d m : ℕ} (hm : 0 < m)
    (h : ∀ i < m, checkChunk P surv fuel d m i = true) : Certified P surv := by
  have hP : paramsOK P = true := by
    have := h 0 hm
    simp only [checkChunk, Bool.and_eq_true] at this
    exact this.1
  refine ⟨hP, fun s ψ a hA => ?_⟩
  obtain ⟨b0, hb0, hF0⟩ := frontier_sound hP hA d _ (root_fits hP hA)
  obtain ⟨i, hi, hbi⟩ := mem_chunkAux hm _ 0 hb0
  have hc := h i hi
  simp only [checkChunk, Bool.and_eq_true, List.all_eq_true] at hc
  exact bnb_sound hP surv fuel b0 (hc.2 b0 hbi) s ψ a hA hF0

end CirclePacking
