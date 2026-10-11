import CirclePacking.Main18
import CirclePacking.Opt18
import CirclePacking.Cert.RB
import CirclePacking.Cert.RB12
import CirclePacking.Cert.RB13
import CirclePacking.Cert.RB14
import CirclePacking.Cert.N18Small
import CirclePacking.Cert.N18K7
import CirclePacking.Cert.N18K8
import CirclePacking.Cert.N18K9
import CirclePacking.Cert.N18K10
import CirclePacking.Cert.N18K11
import CirclePacking.Cert.N18K12
import CirclePacking.Cert.N18K13

/-!
# Optimal packing of 18 unit circles in a circle

**Theorem** (`circle_packing_18`).  Let `R₁₈ = 1 + √2 + √6 = 4.8637033051562731469…`.  Then
1. the explicit configuration `optimal18` (a centre circle, six circles around it, and eleven of the twelve
   circles of the outer ring of the 19-circle packing) packs 18 unit disks in the disk of radius `R₁₈`;
2. 18 unit disks with pairwise disjoint interiors never fit in a disk of radius smaller than `R₁₈`.

So 18 circles need the same container as 19.

Trust base: Lean's kernel, Mathlib, and — for the branch-and-bound certificates in `CirclePacking.Cert.*`
only — the Lean compiler (`native_decide`; one axiom per certificate, see `Check.lean`).
-/

open Real

namespace CirclePacking

theorem n18_certs : ∀ k ≤ 18, 9 ≤ k → Certified (P18 k) (fun _ => false) := by
  intro k hk hk9
  have h := n18small_true
  unfold n18small at h
  simp only [List.all_eq_true, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases (show k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ 14 ≤ k by omega) with
    h1 | h1 | h1 | h1 | h1 | h1
  · subst h1; exact n18_k9
  · subst h1; exact n18_k10
  · subst h1; exact n18_k11
  · subst h1; exact n18_k12
  · subst h1; exact n18_k13
  · exact certified_of_checkRun (h k (by omega))

/-- **Lower bound**, with all certificates discharged. -/
theorem n18_lower' (c : Fin 18 → ℂ) (r : ℝ) (hc : IsPacking c r) : ρ19 ≤ r :=
  n18_lower rb_certs rb12_certs rb13_certs rb14_certs n18_certs n18_k7 n18_k8 c r hc

/-! ### The main theorem -/

/-- **Optimal packing of 18 unit circles in a circle.**  Let `R₁₈ = 1 + √2 + √6` (`R18`).
(1) the explicit configuration `optimal18` packs 18 unit disks (centres pairwise at distance `≥ 2`) in the disk of
radius `R₁₈` about `0`;
(2) if 18 unit disks with centres `c i` have pairwise disjoint interiors (`‖c i - c j‖ ≥ 2`) and lie in the disk of
radius `R` about `z₀`, then `R ≥ R₁₈`. -/
theorem circle_packing_18 :
    ((∀ i, ‖optimal18 i‖ + 1 ≤ R18) ∧ ∀ i j, i ≠ j → 2 ≤ ‖optimal18 i - optimal18 j‖) ∧
    ∀ (c : Fin 18 → ℂ) (z₀ : ℂ) (R : ℝ), (∀ i, ‖c i - z₀‖ + 1 ≤ R) →
      (∀ i j, i ≠ j → 2 ≤ ‖c i - c j‖) → R18 ≤ R := by
  refine ⟨optimal18_packing, fun c z₀ R hR hd => ?_⟩
  have hpk : IsPacking (fun i => c i - z₀) (R - 1) := by
    refine ⟨fun i => by linarith [hR i], fun i j hij => ?_⟩
    simp only [sub_sub_sub_cancel_right]
    exact hd i j hij
  have h1 := n18_lower' _ _ hpk
  rw [R18_eq]
  linarith

/-- **The optimal radius, as an equivalence**: 18 unit disks with pairwise disjoint interiors fit in a disk of
radius `R` if and only if `R ≥ R₁₈`. -/
theorem circle_packing_18_iff (R : ℝ) :
    (∃ c : Fin 18 → ℂ, (∀ i, ‖c i‖ + 1 ≤ R) ∧ ∀ i j, i ≠ j → 2 ≤ ‖c i - c j‖) ↔ R18 ≤ R := by
  obtain ⟨⟨h1, h2⟩, hlow⟩ := circle_packing_18
  refine ⟨fun ⟨c, hc1, hc2⟩ => hlow c 0 R (fun i => by simpa using hc1 i) hc2, fun hR => ?_⟩
  exact ⟨optimal18, fun i => le_trans (h1 i) hR, h2⟩

/-! ### The same theorem in the Euclidean plane `EuclideanSpace ℝ (Fin 2)` -/

/-- **Optimal packing of 18 unit circles in a circle**, for points of `EuclideanSpace ℝ (Fin 2)` with the
Euclidean distance; `optimal18` is read as the points `(x, y)`. -/
theorem circle_packing_18_euclidean :
    ((∀ i, dist !₂[(optimal18 i).re, (optimal18 i).im] 0 + 1 ≤ R18) ∧
      ∀ i j, i ≠ j → 2 ≤ dist !₂[(optimal18 i).re, (optimal18 i).im] !₂[(optimal18 j).re, (optimal18 j).im]) ∧
    ∀ (c : Fin 18 → EuclideanSpace ℝ (Fin 2)) (z₀ : EuclideanSpace ℝ (Fin 2)) (R : ℝ),
      (∀ i, dist (c i) z₀ + 1 ≤ R) → (∀ i j, i ≠ j → 2 ≤ dist (c i) (c j)) → R18 ≤ R := by
  set e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) := Complex.orthonormalBasisOneI.repr
  have he : ∀ z : ℂ, !₂[z.re, z.im] = e z := fun z => rfl
  obtain ⟨⟨h1, h2⟩, hlow⟩ := circle_packing_18
  refine ⟨⟨fun i => ?_, fun i j hij => ?_⟩, fun c z₀ R hR hd => ?_⟩
  · rw [he, ← e.map_zero, LinearIsometryEquiv.dist_map, dist_zero_right]
    exact h1 i
  · rw [he, he, LinearIsometryEquiv.dist_map, dist_eq_norm]
    exact h2 i j hij
  · apply hlow (fun i => e.symm (c i)) (e.symm z₀) R
    · intro i
      rw [← dist_eq_norm, LinearIsometryEquiv.dist_map]
      exact hR i
    · intro i j hij
      rw [← dist_eq_norm, LinearIsometryEquiv.dist_map]
      exact hd i j hij

end CirclePacking
