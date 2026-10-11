import CirclePacking.Main
import CirclePacking.Exact15
import CirclePacking.L7Checks1
import CirclePacking.L7Checks2
import CirclePacking.Cert.RB
import CirclePacking.Cert.N15Small
import CirclePacking.Cert.N15K5
import CirclePacking.Cert.N15K6
import CirclePacking.Cert.N15K7
import CirclePacking.Cert.N15K8
import CirclePacking.Cert.N15K9
import CirclePacking.Cert.N15K10

/-!
# Optimal packing of 15 unit circles in a circle

**Theorem.**  Fifteen non-overlapping unit disks fit in a disk of radius `R` if and only if
`R ≥ 1 + √(6 + 2/√5 + 4 √(1 + 2/√5)) = 4.52135696…`.

Trust base: Lean's kernel, Mathlib, and — for the branch-and-bound certificates in `CirclePacking.Cert.*`
only — the Lean compiler (`native_decide`; one axiom per certificate, see `Check.lean`).
-/

open Real

namespace CirclePacking

theorem n15_certs : ∀ k ≤ 15, k ≠ 5 → Certified (P15 k) (fun _ => false) := by
  intro k hk hk5
  have h := n15small_true
  unfold n15small at h
  simp only [List.all_eq_true, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases (show k ≤ 4 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ 11 ≤ k by omega) with
    h1 | h1 | h1 | h1 | h1 | h1 | h1
  · exact certified_of_checkRun (h k (by omega))
  · subst h1; exact n15_k6
  · subst h1; exact n15_k7
  · subst h1; exact n15_k8
  · subst h1; exact n15_k9
  · subst h1; exact n15_k10
  · exact certified_of_checkRun (h k (by omega))

/-! ### The main theorem -/

/-- **Optimal packing of 15 unit circles in a circle.**
(1) If 15 unit disks with centres `c i` have pairwise disjoint interiors (`‖c i - c j‖ ≥ 2`) and lie in
the disk of radius `R` around `z₀`, then `R ≥ 1 + √(6 + 2/√5 + 4√(1 + 2/√5))`.
(2) The explicit configuration `optimal15` (`CirclePacking.Exact15`) packs 15 unit disks in the disk of this radius
about `0`. -/
theorem circle_packing_15 :
    (∀ (c : Fin 15 → ℂ) (z₀ : ℂ) (R : ℝ), (∀ i, ‖c i - z₀‖ + 1 ≤ R) →
      (∀ i j, i ≠ j → 2 ≤ ‖c i - c j‖) → 1 + √(6 + 2 / √5 + 4 * √(1 + 2 / √5)) ≤ R) ∧
    ((∀ i, ‖optimal15 i‖ + 1 ≤ 1 + √(6 + 2 / √5 + 4 * √(1 + 2 / √5))) ∧
      ∀ i j, i ≠ j → 2 ≤ ‖optimal15 i - optimal15 j‖) := by
  rw [← ρs_closed]
  refine ⟨fun c z₀ R hR hd => ?_, fun i => ?_, fun i j hij => ?_⟩
  · have hp : IsPacking (fun i => c i - z₀) (R - 1) := by
      refine ⟨fun i => by linarith [hR i], fun i j hij => ?_⟩
      simp only [sub_sub_sub_cancel_right]
      exact hd i j hij
    have := n15_lower kktOK_true invOK_true rb_certs n15_certs n15_k5 _ _ hp
    linarith
  · rw [optimal15_eq_Cs]; linarith [cstar_packing.1 i]
  · rw [optimal15_eq_Cs, optimal15_eq_Cs]; exact cstar_packing.2 i j hij

/-- **The optimal radius, as an equivalence.**  Fifteen non-overlapping unit disks fit in a disk of radius
`R` if and only if `R ≥ 1 + √(6 + 2/√5 + 4√(1 + 2/√5))`. -/
theorem circle_packing_15_iff (R : ℝ) :
    (∃ c : Fin 15 → ℂ, (∀ i, ‖c i‖ + 1 ≤ R) ∧ ∀ i j, i ≠ j → 2 ≤ ‖c i - c j‖) ↔
      1 + √(6 + 2 / √5 + 4 * √(1 + 2 / √5)) ≤ R := by
  obtain ⟨hlow, h1, h2⟩ := circle_packing_15
  constructor
  · rintro ⟨d, hd1, hd2⟩
    exact hlow d 0 R (fun i => by simpa using hd1 i) hd2
  · intro hR
    exact ⟨optimal15, fun i => le_trans (h1 i) hR, h2⟩

/-! ### The same theorem in the Euclidean plane `EuclideanSpace ℝ (Fin 2)` -/

/-- **Optimal packing of 15 unit circles in a circle**, for points of `EuclideanSpace ℝ (Fin 2)` with the
Euclidean distance; `optimal15` is read as the points `(x, y)`. -/
theorem circle_packing_15_euclidean :
    (∀ (c : Fin 15 → EuclideanSpace ℝ (Fin 2)) (z₀ : EuclideanSpace ℝ (Fin 2)) (R : ℝ),
      (∀ i, dist (c i) z₀ + 1 ≤ R) → (∀ i j, i ≠ j → 2 ≤ dist (c i) (c j)) →
      1 + √(6 + 2 / √5 + 4 * √(1 + 2 / √5)) ≤ R) ∧
    ((∀ i, dist !₂[(optimal15 i).re, (optimal15 i).im] 0 + 1 ≤ 1 + √(6 + 2 / √5 + 4 * √(1 + 2 / √5))) ∧
      ∀ i j, i ≠ j → 2 ≤ dist !₂[(optimal15 i).re, (optimal15 i).im] !₂[(optimal15 j).re, (optimal15 j).im]) := by
  -- an isometry between `ℂ` and the Euclidean plane
  set e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) := Complex.orthonormalBasisOneI.repr
  have he : ∀ z : ℂ, !₂[z.re, z.im] = e z := fun z => rfl
  obtain ⟨hlow, h1, h2⟩ := circle_packing_15
  refine ⟨fun c z₀ R hR hd => ?_, fun i => ?_, fun i j hij => ?_⟩
  · apply hlow (fun i => e.symm (c i)) (e.symm z₀) R
    · intro i
      rw [← dist_eq_norm, LinearIsometryEquiv.dist_map]
      exact hR i
    · intro i j hij
      rw [← dist_eq_norm, LinearIsometryEquiv.dist_map]
      exact hd i j hij
  · rw [he, ← e.map_zero, LinearIsometryEquiv.dist_map, dist_zero_right]
    exact h1 i
  · rw [he, he, LinearIsometryEquiv.dist_map, dist_eq_norm]
    exact h2 i j hij

end CirclePacking
