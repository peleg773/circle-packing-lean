import CirclePacking.BnB
import C17Surv

/-!
# Two-level chunks

`checkChunk2` (`C17Surv.lean`) splits a chunk of a run further, at a second depth.  Completeness is
`frontier_sound` applied twice.
-/

namespace CirclePacking

theorem certified_of_chunks2 {P : Params} {surv : List IBox → Bool} {fuel d1 m1 : ℕ} (hm1 : 0 < m1)
    (d2 m2 : ℕ → ℕ) (hm2 : ∀ i, 0 < m2 i)
    (h : ∀ i1 < m1, ∀ i2 < m2 i1, checkChunk2 P surv fuel d1 m1 i1 (d2 i1) (m2 i1) i2 = true) :
    Certified P surv := by
  have hP : paramsOK P = true := by
    have := h 0 hm1 0 (hm2 0)
    simp only [checkChunk2, Bool.and_eq_true] at this
    exact this.1
  refine ⟨hP, fun s ψ a hA => ?_⟩
  obtain ⟨b0, hb0, hF0⟩ := frontier_sound hP hA d1 _ (root_fits hP hA)
  obtain ⟨i1, hi1, hbi1⟩ := mem_chunkAux hm1 _ 0 hb0
  obtain ⟨b1, hb1, hF1⟩ := frontier_sound hP hA (d2 i1) b0 hF0
  obtain ⟨i2, hi2, hbi2⟩ := mem_chunkAux (hm2 i1) _ 0 hb1
  have hc := h i1 hi1 i2 hi2
  simp only [checkChunk2, Bool.and_eq_true, List.all_eq_true] at hc
  exact bnb_sound hP surv fuel b1 (hc.2 b0 hbi1 b1 hbi2) s ψ a hA hF1

/-- **Completeness of a chunk tree**: if every leaf computation succeeds, every admissible configuration in
the box `b` lies in a box accepted by `surv`. -/
theorem checkPath_cover {P : Params} (hP : paramsOK P = true) {surv : List IBox → Bool} {fuel : ℕ}
    {s ψ : ℕ → ℝ} {a : Fin (P.n - P.k) → ℝ} (hA : Adm P s ψ a) :
    ∀ (t : CTree) (b : List IBox), t.posOK = true → (∀ p ∈ t.paths, checkPath P surv fuel p b = true) →
      Fits P b s ψ → ∃ b', surv b' = true ∧ Fits P b' s ψ
  | .leaf, b, _, h, hF => by
    have := h [] (by simp [CTree.paths])
    exact bnb_sound hP surv fuel b this s ψ a hA hF
  | .node d m ch, b, hpos, h, hF => by
    simp only [CTree.posOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hpos
    obtain ⟨hm, hch⟩ := hpos
    obtain ⟨b1, hb1, hF1⟩ := frontier_sound hP hA d b hF
    obtain ⟨i, hi, hbi⟩ := mem_chunkAux hm _ 0 hb1
    refine checkPath_cover (fuel := fuel) hP hA (ch i) b1 (hch i hi) (fun p hp => ?_) hF1
    have hq := h ((d, m, i) :: p) (by
      simp only [CTree.paths, List.mem_flatMap, List.mem_range, List.mem_map]
      exact ⟨i, hi, p, hp, rfl⟩)
    simp only [checkPath, List.all_eq_true] at hq
    exact hq b1 hbi

theorem certified_of_tree {P : Params} {surv : List IBox → Bool} {fuel : ℕ} (hP : paramsOK P = true)
    (t : CTree) (hpos : t.posOK = true)
    (h : ∀ n < t.paths.length, checkPath P surv fuel (t.paths.getD n []) (rootBox P) = true) :
    Certified P surv := by
  refine ⟨hP, fun s ψ a hA => checkPath_cover (fuel := fuel) hP hA t _ hpos (fun p hp => ?_) (root_fits hP hA)⟩
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hp
  have := h n hn
  rwa [List.getD_eq_getElem _ _ hn] at this

end CirclePacking
