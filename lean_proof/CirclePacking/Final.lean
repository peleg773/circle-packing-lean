import CirclePacking.Main
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

/-! ### `ρ*` in closed form -/

lemma sqrt5_eq : √5 = 5 - 8 * QK.s5 ^ 2 := by have := QK.s5_sq; linarith

lemma sqrt_cot : √(1 + 2 / √5) = (3 / 2 - 2 * QK.s5 ^ 2) / QK.s5 := by
  have hs := QK.s5_pos
  have hb := QK.s5_bounds
  have hp := QK.s5_poly
  have h5 : 0 < √5 := by positivity
  have hc : 0 < 3 / 2 - 2 * QK.s5 ^ 2 := by
    obtain ⟨-, hh⟩ := hb
    have : QK.s5 ^ 2 ≤ (QK.sHi : ℝ) ^ 2 := pow_le_pow_left₀ hs.le hh 2
    have hv : (QK.sHi : ℝ) ^ 2 < 3 / 4 := by unfold QK.sHi; norm_num
    linarith
  rw [Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)]
  rw [div_pow, eq_div_iff (by positivity)]
  rw [sqrt5_eq] at h5 ⊢
  field_simp
  linear_combination (8 * QK.s5 ^ 2 - 9) * hp

theorem ρs_closed : ρs = √(6 + 2 / √5 + 4 * √(1 + 2 / √5)) := by
  unfold ρs
  congr 1
  have hs := QK.s5_pos
  have hp := QK.s5_poly
  have h5 : 0 < √5 := by positivity
  rw [sqrt_cot]
  rw [sqrt5_eq] at h5 ⊢
  simp only [rho2K, QK.eval]
  push_cast
  field_simp
  linear_combination (96 * QK.s5 ^ 2 + 16 * QK.s5 - 60) * hp

/-! ### The main theorem -/

/-- **Optimal packing of 15 unit circles in a circle.**
(1) If 15 unit disks with centres `c i` have pairwise disjoint interiors (`‖c i - c j‖ ≥ 2`) and lie in
the disk of radius `R` around `z₀`, then `R ≥ 1 + √(6 + 2/√5 + 4√(1 + 2/√5))`.
(2) This radius is attained. -/
theorem circle_packing_15 :
    (∀ (c : Fin 15 → ℂ) (z₀ : ℂ) (R : ℝ), (∀ i, ‖c i - z₀‖ + 1 ≤ R) →
      (∀ i j, i ≠ j → 2 ≤ ‖c i - c j‖) → 1 + √(6 + 2 / √5 + 4 * √(1 + 2 / √5)) ≤ R) ∧
    (∃ c : Fin 15 → ℂ, (∀ i, ‖c i‖ + 1 ≤ 1 + √(6 + 2 / √5 + 4 * √(1 + 2 / √5))) ∧
      ∀ i j, i ≠ j → 2 ≤ ‖c i - c j‖) := by
  rw [← ρs_closed]
  constructor
  · intro c z₀ R hR hd
    have hp : IsPacking (fun i => c i - z₀) (R - 1) := by
      refine ⟨fun i => by linarith [hR i], fun i j hij => ?_⟩
      simp only [sub_sub_sub_cancel_right]
      exact hd i j hij
    have := n15_lower kktOK_true invOK_true rb_certs n15_certs n15_k5 _ _ hp
    linarith
  · exact ⟨fun i => Cs i, fun i => by linarith [cstar_packing.1 i], cstar_packing.2⟩

/-- **The optimal radius, as an equivalence.**  Fifteen non-overlapping unit disks fit in a disk of radius
`R` if and only if `R ≥ 1 + √(6 + 2/√5 + 4√(1 + 2/√5))`. -/
theorem circle_packing_15_iff (R : ℝ) :
    (∃ c : Fin 15 → ℂ, (∀ i, ‖c i‖ + 1 ≤ R) ∧ ∀ i j, i ≠ j → 2 ≤ ‖c i - c j‖) ↔
      1 + √(6 + 2 / √5 + 4 * √(1 + 2 / √5)) ≤ R := by
  obtain ⟨hlow, ⟨c, hc1, hc2⟩⟩ := circle_packing_15
  constructor
  · rintro ⟨d, hd1, hd2⟩
    exact hlow d 0 R (fun i => by simpa using hd1 i) hd2
  · intro hR
    exact ⟨c, fun i => le_trans (hc1 i) hR, hc2⟩

/-! ### The same theorem in the Euclidean plane `EuclideanSpace ℝ (Fin 2)` -/

/-- **Optimal packing of 15 unit circles in a circle**, stated for points of `EuclideanSpace ℝ (Fin 2)`
with the Euclidean distance. -/
theorem circle_packing_15_euclidean :
    (∀ (c : Fin 15 → EuclideanSpace ℝ (Fin 2)) (z₀ : EuclideanSpace ℝ (Fin 2)) (R : ℝ),
      (∀ i, dist (c i) z₀ + 1 ≤ R) → (∀ i j, i ≠ j → 2 ≤ dist (c i) (c j)) →
      1 + √(6 + 2 / √5 + 4 * √(1 + 2 / √5)) ≤ R) ∧
    (∃ c : Fin 15 → EuclideanSpace ℝ (Fin 2), (∀ i, dist (c i) 0 + 1 ≤ 1 + √(6 + 2 / √5 + 4 * √(1 + 2 / √5))) ∧
      ∀ i j, i ≠ j → 2 ≤ dist (c i) (c j)) := by
  -- an isometry between `ℂ` and the Euclidean plane
  set e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) := Complex.orthonormalBasisOneI.repr
  obtain ⟨hlow, hex⟩ := circle_packing_15
  constructor
  · intro c z₀ R hR hd
    apply hlow (fun i => e.symm (c i)) (e.symm z₀) R
    · intro i
      rw [← dist_eq_norm, LinearIsometryEquiv.dist_map]
      exact hR i
    · intro i j hij
      rw [← dist_eq_norm, LinearIsometryEquiv.dist_map]
      exact hd i j hij
  · obtain ⟨c, hc1, hc2⟩ := hex
    refine ⟨fun i => e (c i), fun i => ?_, fun i j hij => ?_⟩
    · rw [← e.map_zero, LinearIsometryEquiv.dist_map, dist_zero_right]
      exact hc1 i
    · rw [LinearIsometryEquiv.dist_map, dist_eq_norm]
      exact hc2 i j hij

end CirclePacking
