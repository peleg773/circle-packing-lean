import CirclePacking.Exact16
import CirclePacking.Cert.RB
import CirclePacking.Cert.RB12
import CirclePacking.Cert.N16Small
import CirclePacking.Cert.N16K5
import CirclePacking.Cert.N16K6
import CirclePacking.Cert.N16K7
import CirclePacking.Cert.N16K8
import CirclePacking.Cert.N16K9
import CirclePacking.Cert.N16K10
import CirclePacking.Cert.N16K11

/-!
# Optimal packing of 16 unit circles in a circle

**Theorem** (`circle_packing_16`).  Let `H16` be the integer polynomial of degree 90 with coefficient list
`H16coeffs` (`CirclePacking.Algebraic16Data`), let `q₁₆` be its largest real root (`q16_isGreatest`; numerically
`0.84699305666011175910546129 < q₁₆ < 0.84699305666011175910546132`), and let
`R₁₆ = 1 + √(2 / (1 - q₁₆)) = 4.61542559487319398553924…` (`R16`).  Then
1. the explicit configuration `optimal16` (`CirclePacking.Exact16`) packs 16 unit disks in the disk of radius `R₁₆`:
   eleven centres on the circle of radius `R₁₆ - 1` at the angles `π + m·arccos q₁₆` (`m = -5, …, 5`), and five
   interior centres `(a, 0)`, `(b, ±c)`, `(d, ±1)` given by explicit formulas in these;
2. 16 unit disks with pairwise disjoint interiors never fit in a disk of radius smaller than `R₁₆`.

Trust base: Lean's kernel, Mathlib, and — for the branch-and-bound certificates in `CirclePacking.Cert.*`
only — the Lean compiler (`native_decide`; one axiom per certificate, see `Check.lean`).
-/

open Real

namespace CirclePacking

theorem n16_certs : ∀ k ≤ 16, k ≠ 5 → Certified (P16 k) (fun _ => false) := by
  intro k hk hk5
  have h := n16small_true
  unfold n16small at h
  simp only [List.all_eq_true, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases (show k ≤ 4 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ 12 ≤ k by omega) with
    h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
  · exact certified_of_checkRun (h k (by omega))
  · subst h1; exact n16_k6
  · subst h1; exact n16_k7
  · subst h1; exact n16_k8
  · subst h1; exact n16_k9
  · subst h1; exact n16_k10
  · subst h1; exact n16_k11
  · exact certified_of_checkRun (h k (by omega))

/-- **Lower bound**, with all certificates discharged. -/
theorem n16_lower' (c : Fin 16 → ℂ) (r : ℝ) (hc : IsPacking c r) : ρ16 ≤ r :=
  n16_lower rb_certs rb12_certs n16_certs n16_k5 c r hc

/-! ### Numerical values -/

/-- decimal brackets of `ρ*` (width `3 · 10⁻²⁵`) -/
def rho16Lo : ℚ := 3615425594873193985539244 / 10 ^ 24
def rho16Hi : ℚ := 36154255948731939855392443 / 10 ^ 25

lemma ρ16_bounds : (rho16Lo : ℝ) ≤ ρ16 ∧ ρ16 ≤ (rho16Hi : ℝ) := by
  have c1 : rho16Lo ^ 2 ≤ P16lo := by decide +kernel
  have c2 : P16hi ≤ rho16Hi ^ 2 := by decide +kernel
  have c3 : (0 : ℚ) ≤ rho16Hi := by decide +kernel
  have c1' := (Rat.cast_le (K := ℝ)).mpr c1
  have c2' := (Rat.cast_le (K := ℝ)).mpr c2
  have c3' := (Rat.cast_le (K := ℝ)).mpr c3
  push_cast at c1' c2' c3'
  obtain ⟨b1, b2⟩ := P16s_bounds
  constructor
  · have : (rho16Lo : ℝ) ^ 2 ≤ ρ16 ^ 2 := by rw [ρ16_sq]; linarith
    exact le_of_pow_le_pow_left₀ two_ne_zero ρ16_pos.le this
  · have : ρ16 ^ 2 ≤ (rho16Hi : ℝ) ^ 2 := by rw [ρ16_sq]; linarith
    exact le_of_pow_le_pow_left₀ two_ne_zero c3' this

/-- `4.615425594873193985539244 ≤ R₁₆ ≤ 4.6154255948731939855392443` -/
theorem R16_bounds : (4615425594873193985539244 / 10 ^ 24 : ℝ) ≤ R16 ∧
    R16 ≤ (46154255948731939855392443 / 10 ^ 25 : ℝ) := by
  obtain ⟨h1, h2⟩ := ρ16_bounds
  have e1 : ((rho16Lo : ℚ) : ℝ) = 3615425594873193985539244 / 10 ^ 24 := by
    unfold rho16Lo; push_cast; ring
  have e2 : ((rho16Hi : ℚ) : ℝ) = 36154255948731939855392443 / 10 ^ 25 := by
    unfold rho16Hi; push_cast; ring
  rw [e1] at h1
  rw [e2] at h2
  rw [R16_eq]
  constructor <;> linarith

/-- `0.84699305666011175910546129 < q₁₆ < 0.84699305666011175910546132` -/
theorem q16_bounds : (84699305666011175910546129 / 10 ^ 26 : ℝ) < q16 ∧
    q16 < (84699305666011175910546132 / 10 ^ 26 : ℝ) := by
  rw [q16_eq_qg]
  obtain ⟨h1, h2⟩ := qg_bounds
  have c1 : (84699305666011175910546129 / 10 ^ 26 : ℚ) < ql16 := by decide +kernel
  have c2 : qh16 < (84699305666011175910546132 / 10 ^ 26 : ℚ) := by decide +kernel
  have c1' := (Rat.cast_lt (K := ℝ)).mpr c1
  have c2' := (Rat.cast_lt (K := ℝ)).mpr c2
  push_cast at c1' c2'
  constructor <;> linarith

/-- the optimum lies within `2⁻⁸⁰` of the rational record configuration `n16ut` (`CirclePacking.N16Data`),
coordinatewise -/
lemma optimal16_near (i : Fin 16) :
    |(optimal16 i).re - n16K.utq (2 * i)| ≤ 1 / 2 ^ 80 ∧ |(optimal16 i).im - n16K.utq (2 * i + 1)| ≤ 1 / 2 ^ 80 := by
  rw [optimal16_eq_C16, ← n16_rb]
  exact ⟨u16_near (by omega), u16_near (by omega)⟩

/-! ### The main theorem -/

/-- **Optimal packing of 16 unit circles in a circle.**  Let `R₁₆ = 1 + √(2 / (1 - q₁₆))` (`R16`), where
`q₁₆ = sSup {x : ℝ | H16(x) = 0}` (`q16`) for the degree-90 integer polynomial `H16` (`H16_natDegree`).
(0) `q₁₆` is the largest real root of `H16`;
(1) the explicit configuration `optimal16` packs 16 unit disks (centres pairwise at distance `≥ 2`) in the disk of
radius `R₁₆` about `0`;
(2) if 16 unit disks with centres `c i` have pairwise disjoint interiors (`‖c i - c j‖ ≥ 2`) and lie in the disk of
radius `R` about `z₀`, then `R ≥ R₁₆`. -/
theorem circle_packing_16 :
    IsGreatest {x : ℝ | Polynomial.aeval x H16 = 0} q16 ∧
    ((∀ i, ‖optimal16 i‖ + 1 ≤ R16) ∧ ∀ i j, i ≠ j → 2 ≤ ‖optimal16 i - optimal16 j‖) ∧
    ∀ (c : Fin 16 → ℂ) (z₀ : ℂ) (R : ℝ), (∀ i, ‖c i - z₀‖ + 1 ≤ R) →
      (∀ i j, i ≠ j → 2 ≤ ‖c i - c j‖) → R16 ≤ R := by
  refine ⟨q16_isGreatest, ⟨fun i => ?_, fun i j hij => ?_⟩, fun c z₀ R hR hd => ?_⟩
  · have := cstar16_packing.1 i
    rw [optimal16_eq_C16, R16_eq]
    simp only at this
    linarith
  · rw [optimal16_eq_C16, optimal16_eq_C16]
    exact cstar16_packing.2 i j hij
  · have hp : IsPacking (fun i => c i - z₀) (R - 1) := by
      refine ⟨fun i => by linarith [hR i], fun i j hij => ?_⟩
      simp only [sub_sub_sub_cancel_right]
      exact hd i j hij
    have := n16_lower' _ _ hp
    rw [R16_eq]
    linarith

/-- **The optimal radius, as an equivalence**: 16 unit disks with pairwise disjoint interiors fit in a disk of
radius `R` if and only if `R ≥ R₁₆`. -/
theorem circle_packing_16_iff (R : ℝ) :
    (∃ c : Fin 16 → ℂ, (∀ i, ‖c i‖ + 1 ≤ R) ∧ ∀ i j, i ≠ j → 2 ≤ ‖c i - c j‖) ↔ R16 ≤ R := by
  obtain ⟨-, ⟨h1, h2⟩, hlow⟩ := circle_packing_16
  refine ⟨fun ⟨c, hc1, hc2⟩ => hlow c 0 R (fun i => by simpa using hc1 i) hc2, fun hR => ?_⟩
  exact ⟨optimal16, fun i => le_trans (h1 i) hR, h2⟩

/-! ### The same theorem in the Euclidean plane `EuclideanSpace ℝ (Fin 2)` -/

/-- **Optimal packing of 16 unit circles in a circle**, for points of `EuclideanSpace ℝ (Fin 2)` with the
Euclidean distance; `optimal16` is read as the points `(x, y)`. -/
theorem circle_packing_16_euclidean :
    ((∀ i, dist !₂[(optimal16 i).re, (optimal16 i).im] 0 + 1 ≤ R16) ∧
      ∀ i j, i ≠ j → 2 ≤ dist !₂[(optimal16 i).re, (optimal16 i).im] !₂[(optimal16 j).re, (optimal16 j).im]) ∧
    ∀ (c : Fin 16 → EuclideanSpace ℝ (Fin 2)) (z₀ : EuclideanSpace ℝ (Fin 2)) (R : ℝ),
      (∀ i, dist (c i) z₀ + 1 ≤ R) → (∀ i j, i ≠ j → 2 ≤ dist (c i) (c j)) → R16 ≤ R := by
  -- an isometry between `ℂ` and the Euclidean plane
  set e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) := Complex.orthonormalBasisOneI.repr
  have he : ∀ z : ℂ, !₂[z.re, z.im] = e z := fun z => rfl
  obtain ⟨-, ⟨h1, h2⟩, hlow⟩ := circle_packing_16
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
