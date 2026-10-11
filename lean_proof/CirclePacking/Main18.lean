import CirclePacking.HexImp18
import CirclePacking.N18CoresOK
import CirclePacking.Count18
import CirclePacking.Radius18
import CirclePacking.Refine
import CirclePacking.Main
import C18Ref

/-!
# Optimal packing of 18 unit circles in a circle: lower bound

`n18_lower`: every packing of 18 unit circles has container parameter `≥ ρ₁₉ = √6 + √2` (given the
branch-and-bound certificates).  Below `ρ₁₉` at most eleven circles touch the container (`card_le_eleven`), so
at least seven are interior; with seven or eight interior circles the search leaves only boxes near rigid
structures of the 19-circle lattice, which are locally unique at `ρ₁₉` (`hex_impossible18`,
`iso_impossible18`); with nine or more nothing survives.
-/

open Real

namespace CirclePacking

/-- `ρ₁₉ = 1 / sin (π/12)` -/
lemma ρ19_eq_inv_sin : ρ19 = 1 / sin (π / 12) := by
  have h22 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h33 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hs : sin (π / 12) ≠ 0 := (sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [pi_pos])).ne'
  rw [eq_div_iff hs, sin_pi_div_twelve]
  unfold ρ19
  have e : (√2 + √2 * √3) * ((-√2 + √2 * √3) / 4) = (√2 * √2) * (√3 * √3 - 1) / 4 := by ring
  rw [e, h22, h33]
  norm_num

lemma two_lt_ρ19 : 2 + ((epsR : ℚ) : ℝ) < ρ19 := by
  rw [epsR_real]
  have h2 : (1.4 : ℝ) < √2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h3 : (1.7 : ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  unfold ρ19
  nlinarith

lemma ρ19_le_P18 (k : ℕ) : ρ19 ≤ sc (P18 k).ρ := by
  have hS := S_pos
  have e : sc (P18 k).ρ = (4248186710296 : ℝ) / (S : ℝ) := by
    show sc 4248186710296 = _; unfold sc; push_cast; ring
  rw [e]
  have hr : ((rho2Hi19 : ℤ) : ℝ) ≤ (4248186710296 : ℝ) ^ 2 := by unfold rho2Hi19; norm_num
  have hsq : ρ19 ^ 2 ≤ ((4248186710296 : ℝ) / (S : ℝ)) ^ 2 := by
    calc ρ19 ^ 2 ≤ ((rho2Hi19 : ℤ) : ℝ) / ((S : ℝ) * S) := ρ19_sq_le
      _ ≤ (4248186710296 : ℝ) ^ 2 / ((S : ℝ) * S) := by gcongr
      _ = _ := by ring
  exact le_of_pow_le_pow_left₀ two_ne_zero (div_nonneg (by norm_num) hS.le) hsq

/-- the run with tolerance `(P18 k).tol` is the run `P18 k` -/
lemma P18T_tol (k : ℕ) : P18T k (S / 16384) = P18 k := rfl

/-- survivors with seven interior circles are impossible below `ρ₁₉` -/
theorem k7_impossible18 {ρ : ℝ} (hρ1 : ρ19 - ((epsR : ℚ) : ℝ) ≤ ρ) (hρ2 : ρ < ρ19) (h2 : 2 ≤ ρ)
    (hρt : ρ ≤ sc (P18 7).ρ) {s ψ : ℕ → ℝ} {a : Fin (18 - 7) → ℝ}
    (hA : AdmR 18 7 ρ (fun m => sc ((P18 7).L m)) s ψ a) {b : List IBox}
    (hb : surv18 7 (P18 7) b = true) (hF : Fits (P18 7) b s ψ) : False := by
  rw [← P18T_tol] at hρt hA hb hF
  unfold surv18 at hb
  rw [ite_eq_left rfl] at hb
  simp only [Bool.or_eq_true] at hb
  rcases hb with (((((hH | hA') | hB) | hC) | hAm) | hBm) | hCm
  · exact hex_impossible18 hρ1 hρ2 h2 hρt hA hH hF
  · exact iso_impossible18 s18A s18ALU s18A_cons s18A_ok s18A_exact s18A_near hρ1 hρ2 h2 hρt hA hA' hF
  · exact iso_impossible18 s18B s18BLU s18B_cons s18B_ok s18B_exact s18B_near hρ1 hρ2 h2 hρt hA hB hF
  · exact iso_impossible18 s18C s18CLU s18C_cons s18C_ok s18C_exact s18C_near hρ1 hρ2 h2 hρt hA hC hF
  · exact iso_impossible18 s18Am s18AmLU s18Am_cons s18Am_ok s18Am_exact s18Am_near hρ1 hρ2 h2 hρt hA hAm hF
  · exact iso_impossible18 s18Bm s18BmLU s18Bm_cons s18Bm_ok s18Bm_exact s18Bm_near hρ1 hρ2 h2 hρt hA hBm hF
  · exact iso_impossible18 s18Cm s18CmLU s18Cm_cons s18Cm_ok s18Cm_exact s18Cm_near hρ1 hρ2 h2 hρt hA hCm hF

/-- survivors with eight interior circles are impossible below `ρ₁₉` -/
theorem k8_impossible18 {ρ : ℝ} (hρ1 : ρ19 - ((epsR : ℚ) : ℝ) ≤ ρ) (hρ2 : ρ < ρ19) (h2 : 2 ≤ ρ)
    (hρt : ρ ≤ sc (P18 8).ρ) {s ψ : ℕ → ℝ} {a : Fin (18 - 8) → ℝ}
    (hA : AdmR 18 8 ρ (fun m => sc ((P18 8).L m)) s ψ a) {b : List IBox}
    (hb : surv18 8 (P18 8) b = true) (hF : Fits (P18 8) b s ψ) : False := by
  rw [← P18T_tol] at hρt hA hb hF
  unfold surv18 at hb
  rw [ite_eq_right (by decide : (8 : ℕ) ≠ 7)] at hb
  simp only [Bool.or_eq_true] at hb
  rcases hb with ((h1 | h2') | h3) | h4
  · exact iso_impossible18 s18K8 s18K8LU s18K8_cons s18K8_ok s18K8_exact s18K8_near hρ1 hρ2 h2 hρt hA h1 hF
  · exact iso_impossible18 s18K8m s18K8mLU s18K8m_cons s18K8m_ok s18K8m_exact s18K8m_near hρ1 hρ2 h2 hρt hA
      h2' hF
  · exact iso_impossible18 s18K8b s18K8bLU s18K8b_cons s18K8b_ok s18K8b_exact s18K8b_near hρ1 hρ2 h2 hρt hA
      h3 hF
  · exact iso_impossible18 s18K8bm s18K8bmLU s18K8bm_cons s18K8bm_ok s18K8bm_exact s18K8bm_near hρ1 hρ2 h2
      hρt hA h4 hF

/-- **Lower bound.** -/
theorem n18_lower
    (hrb : ∀ m, 8 ≤ m → m ≤ 11 → ∀ k ≤ m, Certified (Prb m k) (fun _ => false))
    (h12 : ∀ k ≤ 12, Certified (Prb12 k) (fun _ => false))
    (h13 : ∀ k ≤ 13, Certified (Prb13 k) (fun _ => false))
    (h14 : ∀ k ≤ 14, Certified (Prb14 k) (fun _ => false))
    (hchk : ∀ k ≤ 18, 9 ≤ k → Certified (P18 k) (fun _ => false))
    (hchk7 : Certified (P18 7) (survRef18 7)) (hchk8 : Certified (P18 8) (survRef18 8))
    (c : Fin 18 → ℂ) (r : ℝ) (hc : IsPacking c r) : ρ19 ≤ r := by
  have hRB := radiusBounds18 hrb h12 h13 h14
  by_contra hlt
  push Not at hlt
  have heps : (0 : ℝ) < ((epsR : ℚ) : ℝ) := by rw [epsR_real]; norm_num
  set ρ'' := max r (ρ19 - ((epsR : ℚ) : ℝ)) with hρdef
  have h1 : ρ19 - ((epsR : ℚ) : ℝ) ≤ ρ'' := le_max_right _ _
  have h2 : ρ'' < ρ19 := max_lt hlt (by linarith)
  have h3 : 2 < ρ'' := lt_of_lt_of_le (by linarith [two_lt_ρ19]) h1
  have hcp := hc.mono (le_max_left r (ρ19 - ((epsR : ℚ) : ℝ)))
  obtain ⟨hpk, hIB, -⟩ := pushOut_spec h3 hcp
  obtain ⟨k, hk, s, ψ, a, hA⟩ := exists_canonical (by norm_num) h3 hRB _ hpk hIB
  have hρP : ρ'' ≤ sc (P18 k).ρ := le_trans h2.le (ρ19_le_P18 k)
  -- at most eleven circles touch the container
  have hk7 : 7 ≤ k := by
    have := card_le_eleven (by linarith) (by rw [← ρ19_eq_inv_sin]; exact h2) a hA.bb
    omega
  rcases (show k = 7 ∨ k = 8 ∨ 9 ≤ k by omega) with rfl | rfl | hk9
  · have hc := certified_of_survRef (P := P18 7) (t := S / 262144) (paramsOK_P18T 7 _) hchk7
    have hAd := AdmR.toAdm (P := P18 7) rfl rfl h3.le hρP hA
    obtain ⟨b, hb, hF⟩ := hc.2 _ _ _ hAd
    exact k7_impossible18 h1 h2 h3.le hρP hA hb hF
  · have hc := certified_of_survRef (P := P18 8) (t := S / 262144) (paramsOK_P18T 8 _) hchk8
    have hAd := AdmR.toAdm (P := P18 8) rfl rfl h3.le hρP hA
    obtain ⟨b, hb, hF⟩ := hc.2 _ _ _ hAd
    exact k8_impossible18 h1 h2 h3.le hρP hA hb hF
  · have hAd := AdmR.toAdm (P := P18 k) rfl rfl h3.le hρP hA
    obtain ⟨b, hb, -⟩ := (hchk k hk hk9).2 _ _ _ hAd
    exact absurd hb (by simp)

end CirclePacking
