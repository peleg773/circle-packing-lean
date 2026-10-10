import CirclePacking.Surv
import CirclePacking.Radius

/-!
# Optimal packing of 15 unit circles in a circle: assembly

`n15_lower`: every packing of 15 unit circles has container parameter `≥ ρ*`, given the branch and bound
certificates and the two exact linear-algebra checks of the local uniqueness lemma (all discharged in
`CirclePacking.Final`).  `cstar_packing`: the record configuration `c*` is a packing with parameter `ρ*`.
-/

open Real

namespace CirclePacking

/-! ### Facts about `ρ*` -/

lemma ρs_le_P15 (k : ℕ) : ρs ≤ sc (P15 k).ρ := by
  have h := QK.eval_le_hi rho2K
  have c : QK.hi rho2K ≤ ((3871772928245 : ℚ) / (S : ℚ)) ^ 2 := by decide +kernel
  have c' : (QK.hi rho2K : ℝ) ≤ ((3871772928245 : ℝ) / (S : ℝ)) ^ 2 := by exact_mod_cast c
  have hS := S_pos
  have e : sc (P15 k).ρ = (3871772928245 : ℝ) / (S : ℝ) := by
    show sc 3871772928245 = _; unfold sc; push_cast; ring
  rw [e]
  have hρ := ρs_pos
  have hsq : ρs ^ 2 ≤ ((3871772928245 : ℝ) / (S : ℝ)) ^ 2 := by rw [ρs_sq]; linarith
  exact le_of_pow_le_pow_left₀ two_ne_zero (div_nonneg (by norm_num) hS.le) hsq

lemma epsR_real : ((epsR : ℚ) : ℝ) = 1 / 1000000 := by unfold epsR; push_cast; ring

lemma two_lt_ρs : 2 + ((epsR : ℚ) : ℝ) < ρs := by
  rw [epsR_real]
  have h := QK.lo_le_eval rho2K
  have c : ((2 : ℚ) + 1 / 1000000) ^ 2 < QK.lo rho2K := by decide +kernel
  have c' := (Rat.cast_lt (K := ℝ)).mpr c
  push_cast at c'
  have hρ := ρs_pos
  have hsq : ((2 : ℝ) + 1 / 1000000) ^ 2 < ρs ^ 2 := by rw [ρs_sq]; linarith
  exact lt_of_pow_lt_pow_left₀ 2 hρ.le hsq

/-! ### The radius bounds for `m < 15` -/

theorem radiusBounds15
    (hrb : ∀ m, 8 ≤ m → m ≤ 11 → ∀ k ≤ m, Certified (Prb m k) (fun _ => false)) :
    RadiusBounds 15 (fun m => sc (Ltab m)) := by
  have r8 : RB 8 := rb_bnb (by norm_num)
    (fun m' h0 hlt => by
      interval_cases m'
      exacts [rb1, rb2, rb3, rb4, rb5, rb6, rb7])
    (by decide) rfl (hrb 8 le_rfl (by norm_num))
  have r9 : RB 9 := rb_bnb (by norm_num)
    (fun m' h0 hlt => by
      interval_cases m'
      exacts [rb1, rb2, rb3, rb4, rb5, rb6, rb7, r8])
    (by decide) rfl (hrb 9 (by norm_num) (by norm_num))
  have r10 : RB 10 := rb_bnb (by norm_num)
    (fun m' h0 hlt => by
      interval_cases m'
      exacts [rb1, rb2, rb3, rb4, rb5, rb6, rb7, r8, r9])
    (by decide) rfl (hrb 10 (by norm_num) (by norm_num))
  have r11 : RB 11 := rb_bnb (by norm_num)
    (fun m' h0 hlt => by
      interval_cases m'
      exacts [rb1, rb2, rb3, rb4, rb5, rb6, rb7, r8, r9, r10])
    (by decide) rfl (hrb 11 (by norm_num) le_rfl)
  have r12 : RB 12 := rb_restrict (m' := 11) (by norm_num) (le_of_eq rfl) r11
  have r13 : RB 13 := rb_restrict (m' := 11) (by norm_num) (le_of_eq rfl) r11
  have r14 : RB 14 := rb_restrict (m' := 11) (by norm_num) (le_of_eq rfl) r11
  intro m h0 hlt d r hd
  interval_cases m
  exacts [rb1 d r hd, rb2 d r hd, rb3 d r hd, rb4 d r hd, rb5 d r hd, rb6 d r hd, rb7 d r hd, r8 d r hd,
    r9 d r hd, r10 d r hd, r11 d r hd, r12 d r hd, r13 d r hd, r14 d r hd]

/-! ### The lower bound -/

/-- **Lower bound.**  Every packing of 15 unit circles (centres in the disk of radius `r`, pairwise
distances `≥ 2`) has `r ≥ ρ*`. -/
theorem n15_lower (hK : kktOK = true) (hInv : invOK = true)
    (hrb : ∀ m, 8 ≤ m → m ≤ 11 → ∀ k ≤ m, Certified (Prb m k) (fun _ => false))
    (hchk : ∀ k ≤ 15, k ≠ 5 → Certified (P15 k) (fun _ => false))
    (hchk5 : Certified (P15 5) (survOK (P15 5)))
    (c : Fin 15 → ℂ) (r : ℝ) (hc : IsPacking c r) : ρs ≤ r := by
  have hRB := radiusBounds15 hrb
  by_contra hlt
  push Not at hlt
  have heps : (0 : ℝ) < ((epsR : ℚ) : ℝ) := by rw [epsR_real]; norm_num
  set ρ'' := max r (ρs - ((epsR : ℚ) : ℝ)) with hρdef
  have h1 : ρs - ((epsR : ℚ) : ℝ) ≤ ρ'' := le_max_right _ _
  have h2 : ρ'' < ρs := max_lt hlt (by linarith)
  have h3 : 2 < ρ'' := lt_of_lt_of_le (by linarith [two_lt_ρs]) h1
  have hcp := hc.mono (le_max_left r (ρs - ((epsR : ℚ) : ℝ)))
  obtain ⟨hpk, hIB, -⟩ := pushOut_spec h3 hcp
  obtain ⟨k, hk, s, ψ, a, hA⟩ := exists_canonical (by norm_num) h3 hRB _ hpk hIB
  have hρP : ρ'' ≤ sc (P15 k).ρ := le_trans h2.le (ρs_le_P15 k)
  by_cases hk5 : k = 5
  · subst hk5
    have hAd := AdmR.toAdm (P := P15 5) rfl rfl h3.le hρP hA
    obtain ⟨b, hb, hF⟩ := hchk5.2 _ _ _ hAd
    exact k5_impossible hK hInv h1 h2 h3.le hρP hA hb hF
  · have hAd := AdmR.toAdm (P := P15 k) rfl rfl h3.le hρP hA
    obtain ⟨b, hb, -⟩ := (hchk k hk hk5).2 _ _ _ hAd
    exact absurd hb (by simp)

/-! ### `c*` is a packing -/

/-- squared distance of two points of `c*`, in `K` -/
def dsqK (p q : ℕ) : QK := (cx p - cx q) * (cx p - cx q) + (cy p - cy q) * (cy p - cy q)

def cstarOK : Bool :=
  (List.range 15).all (fun p =>
    (decide (cx p * cx p + cy p * cy p = rho2K) || decide (QK.hi (cx p * cx p + cy p * cy p) ≤ QK.lo rho2K)) &&
    (List.range 15).all (fun q => decide (p = q) || decide (dsqK p q = 4) || decide (4 ≤ QK.lo (dsqK p q))))

set_option maxRecDepth 100000 in
theorem cstarOK_true : cstarOK = true := by decide +kernel

lemma Cs_norm_sq (p : ℕ) : ‖Cs p‖ ^ 2 = (cx p * cx p + cy p * cy p).eval := by
  rw [sq_norm_eq]; simp [Cs]; ring

lemma Cs_dist_sq (p q : ℕ) : ‖Cs p - Cs q‖ ^ 2 = (dsqK p q).eval := by
  rw [sq_norm_eq]; simp [Cs, dsqK]; ring

theorem cstar_packing : IsPacking (fun i : Fin 15 => Cs i) ρs := by
  have h := cstarOK_true
  unfold cstarOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  have hρ := ρs_pos
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · have hn : ‖Cs i‖ ^ 2 ≤ ρs ^ 2 := by
      rw [Cs_norm_sq, ρs_sq]
      rcases (h i i.isLt).1 with he | hle
      · rw [he]
      · have h1 := QK.eval_le_hi (cx i * cx i + cy i * cy i)
        have h2 := QK.lo_le_eval rho2K
        have h3 : (QK.hi (cx i * cx i + cy i * cy i) : ℝ) ≤ (QK.lo rho2K : ℝ) := by exact_mod_cast hle
        linarith
    exact le_of_pow_le_pow_left₀ two_ne_zero hρ.le hn
  · have hne : (i : ℕ) ≠ j := fun h' => hij (Fin.ext h')
    have hd : 4 ≤ ‖Cs i - Cs j‖ ^ 2 := by
      rw [Cs_dist_sq]
      rcases (h i i.isLt).2 j j.isLt with (he | he) | hle
      · exact absurd he hne
      · rw [he, show (4 : QK).eval = 4 by show (QK.ofQ 4).eval = 4; simp]
      · have h1 := QK.lo_le_eval (dsqK i j)
        have h3 : (4 : ℝ) ≤ (QK.lo (dsqK i j) : ℝ) := by exact_mod_cast hle
        linarith
    nlinarith [norm_nonneg (Cs i - Cs j)]

end CirclePacking
