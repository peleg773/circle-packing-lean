import CirclePacking.CStar

/-!
# Survivors of the record case are close to `c*` (lemma L8)

For a survivor box list of the `k = 5` run that passes `survOK`, every admissible configuration in it has
its ten boundary points in ten disjoint windows, one per window, and is then within squared distance
`R2` of `c*`, so the local uniqueness theorem applies.
-/

open Real Finset

namespace CirclePacking

/-! ### Sums of optional rationals -/

lemma sumOpt_spec : ∀ {l : List (Option ℚ)} {T : ℚ}, sumOpt l = some T →
    (∀ x ∈ l, x.isSome) ∧ T = (l.map (fun x => x.getD 0)).sum
  | [], T, h => by
    simp only [sumOpt, Option.some.injEq] at h
    simp [← h]
  | none :: l, T, h => by simp [sumOpt] at h
  | some x :: l, T, h => by
    simp only [sumOpt, Option.map_eq_some_iff] at h
    obtain ⟨u, hu, rfl⟩ := h
    obtain ⟨h1, h2⟩ := sumOpt_spec hu
    refine ⟨?_, ?_⟩
    · intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · rfl
      · exact h1 y hy
    · simp [h2]

lemma list_sum_map_range (n : ℕ) (g : ℕ → ℚ) : ((List.range n).map g).sum = ∑ i ∈ range n, g i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

lemma sumOpt_range {n : ℕ} {f : ℕ → Option ℚ} {T : ℚ} (h : sumOpt ((List.range n).map f) = some T) :
    (∀ i < n, f i = some ((f i).getD 0)) ∧ T = ∑ i ∈ range n, (f i).getD 0 := by
  obtain ⟨h1, h2⟩ := sumOpt_spec h
  refine ⟨?_, ?_⟩
  · intro i hi
    have := h1 (f i) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    rw [Option.isSome_iff_exists] at this
    obtain ⟨q, hq⟩ := this
    simp [hq]
  · rw [h2, List.map_map]
    exact list_sum_map_range n _

/-! ### Covering the circle by windows and bad intervals -/

lemma exists_window (c : ℕ → ℝ) (n : ℕ) {x : ℝ} (h0 : c 0 ≤ x) (hn : x ≤ c (n + 1)) :
    ∃ w ≤ n, c w ≤ x ∧ x ≤ c (w + 1) := by
  induction n with
  | zero => exact ⟨0, le_refl _, h0, hn⟩
  | succ n ih =>
    by_cases hx : x ≤ c (n + 1)
    · obtain ⟨w, hw, h1, h2⟩ := ih hx
      exact ⟨w, by omega, h1, h2⟩
    · exact ⟨n + 1, le_refl _, (not_le.mp hx).le, hn⟩

lemma sc_wStart_ten (P : Params) (arcs : List (ℤ × ℤ)) :
    sc (wStart P arcs 10) = sc (win P arcs 0).1 + 1 := by
  simp [wStart, sc_add, sc_S]

lemma wStart_lt {P : Params} {arcs : List (ℤ × ℤ)} {w : ℕ} (hw : w < 10) :
    wStart P arcs w = (win P arcs w).1 := by
  simp [wStart, show w ≠ 10 by omega]

/-- **Assignment of the boundary points to the windows.** -/
theorem surv_assign {P : Params} {arcs : List (ℤ × ℤ)} (hδ : 0 < P.δ)
    (hbad : ∀ w < 10, badOK arcs P.δ P.jf (badI P arcs w) = true)
    (hwid : ∀ w < 10, (win P arcs w).2 - (win P arcs w).1 < P.δ)
    (a : Fin 10 → ℝ)
    (hsep : ∀ b b', b ≠ b' → ∀ m : ℤ, sc P.δ ≤ |a b - a b' - m|)
    (hall : ∀ b, ∀ p ∈ arcs, Avoids (a b) p) :
    ∃ σ : Fin 10 → Fin 10, Function.Injective σ ∧ ∀ w : Fin 10, ∃ m : ℤ,
      sc (win P arcs w).1 ≤ a (σ w) + m ∧ a (σ w) + m ≤ sc (win P arcs w).2 := by
  -- every boundary point lies in some window
  have hin : ∀ b : Fin 10, ∃ w : Fin 10, ∃ m : ℤ,
      sc (win P arcs w).1 ≤ a b + m ∧ a b + m ≤ sc (win P arcs w).2 := by
    intro b
    set L := sc (win P arcs 0).1
    set m : ℤ := ⌈L - a b⌉
    have hm1 : L ≤ a b + m := by have := Int.le_ceil (L - a b); linarith
    have hm2 : a b + m ≤ L + 1 := by have := Int.ceil_lt_add_one (L - a b); linarith
    have h0 : sc (wStart P arcs 0) ≤ a b + m := by rw [wStart_lt (by norm_num)]; exact hm1
    have h10 : a b + m ≤ sc (wStart P arcs (9 + 1)) := by rw [sc_wStart_ten]; exact hm2
    obtain ⟨w, hw, hw1, hw2⟩ := exists_window (fun w => sc (wStart P arcs w)) 9 h0 h10
    rw [wStart_lt (by omega)] at hw1
    by_cases hx : a b + m ≤ sc (win P arcs w).2
    · exact ⟨⟨w, by omega⟩, m, hw1, hx⟩
    · exfalso
      have hx' : sc (badI P arcs w).1 ≤ a b + m := by simp only [badI]; linarith
      have hx'' : a b + m ≤ sc (badI P arcs w).2 := by simp only [badI]; exact hw2
      have hb := hbad w (by omega)
      unfold badOK at hb
      simp only [Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq] at hb
      rcases hb with ⟨q, hq, hq1, hq2⟩ | hg
      · have hav : ∀ p ∈ arcs, Avoids (a b + m) p := fun p hp => (hall b p hp).shift m
        exact avoids_lift hav q hq ⟨lt_of_lt_of_le (sc_lt_iff.mpr hq1) hx',
          lt_of_le_of_lt hx'' (sc_lt_iff.mpr hq2)⟩
      · have := card_le_greedyFromInterval arcs P.δ (badI P arcs w).1 (badI P arcs w).2 hδ P.jf 9
          (by norm_num) a hsep hall b m hx' hx''
        omega
  choose wf mf hwf using hin
  -- at most one point per window
  have hinj : Function.Injective wf := by
    intro b b' heq
    by_contra hne
    have h1 := hwf b
    have h2 := hwf b'
    rw [heq] at h1
    have hw := hwid (wf b') (wf b').isLt
    have hwR : sc (win P arcs (wf b')).2 - sc (win P arcs (wf b')).1 < sc P.δ := by
      rw [← sc_sub]; exact sc_lt_iff.mpr hw
    have hs := hsep b b' hne (mf b' - mf b)
    push_cast at hs
    have : |a b - a b' - (mf b' - mf b)| < sc P.δ := by
      rw [abs_lt]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    linarith
  have hbij : Function.Bijective wf := Finite.injective_iff_bijective.mp hinj
  set e := Equiv.ofBijective wf hbij
  refine ⟨e.symm, e.symm.injective, ?_⟩
  intro w
  have h := hwf (e.symm w)
  have he : wf (e.symm w) = w := e.apply_symm_apply w
  rw [he] at h
  exact ⟨_, h⟩

/-! ### Closeness of a single point -/

lemma corner_val (x y c : ℤ) :
    sc x ^ 2 + sc y ^ 2 - 2 * sc c * sc x * sc y =
      ((x * x * S + y * y * S - 2 * c * x * y : ℤ) : ℝ) / ((S : ℝ) * S * S) := by
  have hS := S_pos
  unfold sc; push_cast; field_simp

lemma corner_le {x y c M : ℤ} (h : x * x * S + y * y * S - 2 * c * x * y ≤ M) :
    sc x ^ 2 + sc y ^ 2 - 2 * sc c * sc x * sc y ≤ (M : ℝ) / ((S : ℝ) * S * S) := by
  rw [corner_val]
  apply div_le_div_of_nonneg_right _ S3_pos.le
  exact_mod_cast h

lemma fifth_bounds (j : ℕ) : sc (fifthLo j) ≤ (j : ℝ) / 5 ∧ (j : ℝ) / 5 ≤ sc (fifthHi j) := by
  have hS := S_pos
  have h1 := ediv_le_div ((j : ℤ) * S) 5 (by norm_num)
  have h2 := div_le_ceilDiv ((j : ℤ) * S) 5 (by norm_num)
  push_cast at h1 h2
  unfold sc fifthLo fifthHi
  constructor
  · rw [div_le_div_iff₀ hS (by norm_num)]
    have := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 5)
    have e : (j : ℝ) * S / 5 * 5 = j * S := by field_simp
    nlinarith
  · rw [div_le_div_iff₀ (by norm_num) hS]
    have := mul_le_mul_of_nonneg_right h2 (by norm_num : (0 : ℝ) ≤ 5)
    have e : (j : ℝ) * S / 5 * 5 = j * S := by field_simp
    nlinarith

lemma interiorErr_sound {I : IBox} {j : ℕ} {e : ℚ} (h : interiorErr I j = some e) {s ψ : ℝ}
    (hI : InI I s ψ) : ‖polar s ψ - polar r5 (j / 5)‖ ^ 2 ≤ e := by
  unfold interiorErr at h
  simp only at h
  split_ifs at h with hc
  obtain ⟨hD0, hD1, hslo⟩ := hc
  simp only [Option.some.injEq] at h
  subst h
  set D := max (I.phi - fifthLo j) (fifthHi j - I.plo) with hD
  obtain ⟨hI1, hI2, hI3, hI4⟩ := hI
  have hs0 : 0 ≤ s := le_trans (sc_nonneg hslo) hI1
  obtain ⟨hr1, hr2⟩ := r5_bounds
  have hr0 : 0 < r5 := lt_of_lt_of_le (sc_pos (by decide)) hr1
  obtain ⟨hf1, hf2⟩ := fifth_bounds j
  have hdist : |ψ - j / 5 - ((0 : ℤ) : ℝ)| ≤ sc D := by
    rw [Int.cast_zero, sub_zero, abs_le]
    have h1 : sc (I.phi - fifthLo j) ≤ sc D := sc_le_iff.mpr (le_max_left _ _)
    have h2 : sc (fifthHi j - I.plo) ≤ sc D := sc_le_iff.mpr (le_max_right _ _)
    rw [sc_sub] at h1 h2
    constructor <;> linarith
  have hcos1 := cos_turn_le (half_of_two_le hD1) hdist
  have hcos2 := cosZ_sc hD0 hD1
  rw [normSq_polar_sub]
  have hprod : 0 ≤ s * r5 := mul_nonneg hs0 hr0.le
  have step : s ^ 2 + r5 ^ 2 - 2 * s * r5 * Real.cos (2 * π * (ψ - j / 5)) ≤
      s ^ 2 + r5 ^ 2 - 2 * sc (cosZ D) * s * r5 := by
    nlinarith [mul_le_mul_of_nonneg_left (le_trans hcos2 hcos1) hprod]
  refine le_trans step ?_
  simp only [Rat.cast_div, Rat.cast_intCast, Rat.cast_mul, Int.cast_mul]
  apply Q_le_corners hI1 hI2 hr1 hr2 <;> apply corner_le
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  · exact le_trans (le_max_left _ _) (le_max_right _ _)
  · exact le_trans (le_max_right _ _) (le_max_right _ _)

/-- `c*`'s boundary point `w` in polar form with a certified angle bracket -/
lemma Cs_boundary {w : ℕ} (hw : w < 10) :
    ∃ θ, Cs (5 + w) = polar ρs θ ∧ sc (thetaLo w) ≤ θ ∧ θ ≤ sc (thetaHi w) := by
  obtain ⟨hα1, hα2⟩ := And.intro αs_ge αs_le
  rcases Nat.even_or_odd' w with ⟨j, rfl | rfl⟩
  · refine ⟨αs + j / 5, Cs_p (by omega), ?_, ?_⟩
    · have h2 : (2 * j) % 2 = 0 := by omega
      have h3 : 2 * j / 2 = j := by omega
      simp only [thetaLo, h2, h3, ite_true, sc_add]
      linarith [(fifth_bounds j).1]
    · have h2 : (2 * j) % 2 = 0 := by omega
      have h3 : 2 * j / 2 = j := by omega
      simp only [thetaHi, h2, h3, ite_true, sc_add]
      linarith [(fifth_bounds j).2]
  · refine ⟨(j + 1) / 5 - αs, ?_, ?_, ?_⟩
    · rw [show 5 + (2 * j + 1) = 6 + 2 * j by ring]; exact Cs_q (by omega)
    · have h2 : (2 * j + 1) % 2 = 1 := by omega
      have h3 : (2 * j + 1) / 2 = j := by omega
      simp only [thetaLo, h2, h3, show (1 : ℕ) ≠ 0 by norm_num, ite_false, sc_sub]
      have := (fifth_bounds (j + 1)).1
      push_cast at this
      linarith
    · have h2 : (2 * j + 1) % 2 = 1 := by omega
      have h3 : (2 * j + 1) / 2 = j := by omega
      simp only [thetaHi, h2, h3, show (1 : ℕ) ≠ 0 by norm_num, ite_false, sc_sub]
      have := (fifth_bounds (j + 1)).2
      push_cast at this
      linarith

lemma boundaryErr_sound {W : ℤ × ℤ} {w : ℕ} (hw : w < 10) {e : ℚ} (h : boundaryErr W w = some e)
    {ρ y : ℝ} (hρ1 : ρs - epsR ≤ ρ) (hρ2 : ρ ≤ ρs) (hρ0 : 0 ≤ ρ) (hy1 : sc W.1 ≤ y) (hy2 : y ≤ sc W.2) :
    ‖polar ρ y - Cs (5 + w)‖ ^ 2 ≤ e := by
  unfold boundaryErr at h
  simp only at h
  split_ifs at h with hc
  obtain ⟨hD0, hD1⟩ := hc
  simp only [Option.some.injEq] at h
  subst h
  set D := max (W.2 - thetaLo w) (thetaHi w - W.1) with hD
  obtain ⟨θ, hθ, hθ1, hθ2⟩ := Cs_boundary hw
  rw [hθ, normSq_polar_sub]
  have hdist : |y - θ - ((0 : ℤ) : ℝ)| ≤ sc D := by
    rw [Int.cast_zero, sub_zero, abs_le]
    have h1 : sc (W.2 - thetaLo w) ≤ sc D := sc_le_iff.mpr (le_max_left _ _)
    have h2 : sc (thetaHi w - W.1) ≤ sc D := sc_le_iff.mpr (le_max_right _ _)
    rw [sc_sub] at h1 h2
    constructor <;> linarith
  have hcos1 := cos_turn_le (half_of_two_le hD1) hdist
  have hcos2 := cosZ_sc hD0 hD1
  have hρs := ρs_pos
  have hrho := rho2_le
  set C := Real.cos (2 * π * (y - θ))
  have hC1 : C ≤ 1 := Real.cos_le_one _
  have hcC : sc (cosZ D) ≤ C := le_trans hcos2 hcos1
  have hS := S_pos
  have heps : ((epsR : ℚ) : ℝ) = 1 / 1000000 := by unfold epsR; push_cast; ring
  -- (ρs - ρ)² + 2 ρ ρs (1 - C)
  have e1 : ρ ^ 2 + ρs ^ 2 - 2 * ρ * ρs * C = (ρs - ρ) ^ 2 + 2 * (ρ * ρs) * (1 - C) := by ring
  rw [e1]
  have h1 : (ρs - ρ) ^ 2 ≤ ((epsR : ℚ) : ℝ) ^ 2 := by
    rw [heps]; have : ρs - ρ ≤ 1 / 1000000 := by rw [heps] at hρ1; linarith
    nlinarith
  have h2 : 2 * (ρ * ρs) * (1 - C) ≤ 2 * ρs ^ 2 * (1 - sc (cosZ D)) := by
    have : ρ * ρs ≤ ρs ^ 2 := by nlinarith
    have : 0 ≤ ρ * ρs := by positivity
    nlinarith
  have h3 : 2 * ρs ^ 2 * (1 - sc (cosZ D)) ≤ 2 * ((rho2Hi : ℝ) / ((S : ℝ) * S)) * (1 - sc (cosZ D)) := by
    have : 0 ≤ 1 - sc (cosZ D) := by linarith
    nlinarith
  have e2 : 2 * ((rho2Hi : ℝ) / ((S : ℝ) * S)) * (1 - sc (cosZ D)) =
      ((2 * rho2Hi * (S - cosZ D) : ℤ) : ℝ) / ((S : ℝ) * S * S) := by
    unfold sc; push_cast; field_simp
  push_cast
  rw [e2] at h3
  push_cast at h3
  have : ((epsR : ℚ) : ℝ) * ((epsR : ℚ) : ℝ) = ((epsR : ℚ) : ℝ) ^ 2 := by ring
  linarith

/-! ### The record case `k = 5` -/

lemma paramsOK_congr {P Q : Params} (h1 : P.ρ = Q.ρ) (h2 : P.Rhi = Q.Rhi) (h3 : P.δ = Q.δ) :
    paramsOK P = paramsOK Q := by
  unfold paramsOK; rw [h1, h2, h3]

theorem paramsOK_P15_0 : paramsOK (P15 0) = true := by decide +kernel

theorem paramsOK_P15 (k : ℕ) : paramsOK (P15 k) = true := by
  rw [paramsOK_congr (P := P15 k) (Q := P15 0) rfl rfl rfl]; exact paramsOK_P15_0

lemma bdi_eq {t : ℕ} (ht : t < 10) : bdi t = 5 + t := by
  have : ∀ t < 10, bdi t = 5 + t := by decide
  exact this t ht

lemma R2_eq : R2 = survR2 := rfl

/-- squared norm in coordinates -/
lemma sq_norm_eq (w : ℂ) : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

/-- **Lemma L8 + L7.**  No admissible configuration with `k = 5` interior points and container radius
`ρ ∈ [ρ* - epsR, ρ*)` lies in a box list passing `survOK`. -/
theorem k5_impossible (hK : kktOK = true) (hInv : invOK = true)
    {ρ : ℝ} (hρ1 : ρs - epsR ≤ ρ) (hρ2 : ρ < ρs) (h2 : 2 ≤ ρ) (hρt : ρ ≤ sc (P15 5).ρ)
    {s ψ : ℕ → ℝ} {a : Fin (15 - 5) → ℝ}
    (hA : AdmR 15 5 ρ (fun m => sc ((P15 5).L m)) s ψ a) {bx : List IBox}
    (hS : survOK (P15 5) bx = true) (hF : Fits (P15 5) bx s ψ) : False := by
  set P := P15 5 with hPdef
  have hP : paramsOK P = true := paramsOK_P15 5
  obtain ⟨hρP, -, -, hδ0, hδ1, hδc⟩ := paramsOK_facts hP
  have hAd := AdmR.toAdm (P := P) rfl rfl h2 hρt hA
  have hρ0 : 0 ≤ ρ := by linarith
  obtain ⟨hlen, hin⟩ := hF
  have hlen5 : bx.length = 5 := hlen
  -- unpack `survOK`
  unfold survOK at hS
  cases harcs : survArcs P bx with
  | none => rw [harcs] at hS; simp at hS
  | some arcs =>
  rw [harcs] at hS
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hS
  obtain ⟨⟨hbad, hwid⟩, hclose⟩ := hS
  unfold survArcs at harcs
  split_ifs at harcs with hok
  simp only [Option.some.injEq] at harcs
  simp only [List.all_eq_true, List.mem_range] at hok
  -- boundary points avoid the arcs and are separated
  have hall : ∀ b : Fin 10, ∀ p ∈ arcs, Avoids (a b) p := by
    intro b p hp
    rw [← harcs] at hp
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
    have hj5 := List.mem_range.mp hj
    have hinj : InI (gI bx j) (s j) (ψ j) := hin j (by omega)
    exact arc_avoids (hok j hj5) hρP hinj (hAd.s_sq j hj5) (hAd.ib b j hj5)
  have hsep : ∀ b b' : Fin 10, b ≠ b' → ∀ m : ℤ, sc P.δ ≤ |a b - a b' - m| :=
    fun b b' hbb m => sep_of_cos hρP hδ0.le hδ1 hδc (hAd.bb b b' hbb) m
  obtain ⟨σ, hσ, hwin⟩ := surv_assign hδ0 hbad (fun w hw => hwid w hw) (fun b => a b) hsep hall
  choose mw hmw using hwin
  -- the configuration in the labelling of `c*`
  let bang : ℕ → ℝ := fun w => if h : w < 10 then a (σ ⟨w, h⟩) else 0
  let Z : ℕ → ℂ := fun p => if p < 5 then polar (s p) (ψ p) else polar ρ (bang (p - 5))
  let z : ℕ → ℝ := fun c => if c % 2 = 0 then (Z (c / 2)).re else (Z (c / 2)).im
  have hz0 : ∀ p, z (2 * p) = (Z p).re := by
    intro p; simp only [z]; rw [if_pos (by omega), show 2 * p / 2 = p by omega]
  have hz1 : ∀ p, z (2 * p + 1) = (Z p).im := by
    intro p; simp only [z]; rw [if_neg (by omega), show (2 * p + 1) / 2 = p by omega]
  have hZi : ∀ p < 5, Z p = polar (s p) (ψ p) := fun p hp => by simp only [Z]; rw [if_pos hp]
  have hZb : ∀ w : Fin 10, Z (5 + w) = polar ρ (a (σ w)) := by
    intro w
    simp only [Z, bang]
    rw [if_neg (by omega), dif_pos (by omega)]
    congr 3
    ext; simp
  -- pairwise distances
  have hsep2 : ∀ p < 15, ∀ q < 15, p ≠ q → 4 ≤ ‖Z p - Z q‖ ^ 2 := by
    have hib : ∀ j < 5, ∀ w : Fin 10, 4 ≤ ‖polar (s j) (ψ j) - polar ρ (a (σ w))‖ ^ 2 := by
      intro j hj w
      rw [normSq_polar_sub]
      have h := hA.ib (σ w) j hj
      have e : Real.cos (2 * π * (ψ j - a (σ w))) = Real.cos (2 * π * (a (σ w) - ψ j)) := by
        rw [← Real.cos_neg]; ring_nf
      rw [e]; linarith
    intro p hp q hq hpq
    by_cases hp5 : p < 5 <;> by_cases hq5 : q < 5
    · rw [hZi p hp5, hZi q hq5, normSq_polar_sub]
      exact hA.ii p hp5 q hq5 hpq
    · obtain ⟨w, rfl⟩ : ∃ w : Fin 10, q = 5 + w := ⟨⟨q - 5, by omega⟩, by simp; omega⟩
      rw [hZi p hp5, hZb w]
      exact hib p hp5 w
    · obtain ⟨w, rfl⟩ : ∃ w : Fin 10, p = 5 + w := ⟨⟨p - 5, by omega⟩, by simp; omega⟩
      rw [hZi q hq5, hZb w, norm_sub_rev]
      exact hib q hq5 w
    · obtain ⟨w, rfl⟩ : ∃ w : Fin 10, p = 5 + w := ⟨⟨p - 5, by omega⟩, by simp; omega⟩
      obtain ⟨w', rfl⟩ : ∃ w : Fin 10, q = 5 + w := ⟨⟨q - 5, by omega⟩, by simp; omega⟩
      rw [hZb w, hZb w', normSq_polar_sub]
      have hww : w ≠ w' := by intro h; apply hpq; rw [h]
      have h := hA.bb (σ w) (σ w') (fun h => hww (hσ h))
      linarith
  -- the hypotheses of the local uniqueness theorem
  have hc : ∀ r < 20, 4 ≤ (z (2 * (ctc r).1) - z (2 * (ctc r).2)) ^ 2 +
      (z (2 * (ctc r).1 + 1) - z (2 * (ctc r).2 + 1)) ^ 2 := by
    intro r hr
    obtain ⟨hi, hj, hij, -⟩ := contactsOK_spec contactsOK_true hr
    rw [hz0, hz0, hz1, hz1]
    have := hsep2 _ hi _ hj hij
    rw [sq_norm_eq] at this
    simpa using this
  have hb : ∀ t < 10, z (2 * bdi t) ^ 2 + z (2 * bdi t + 1) ^ 2 ≤ rho2K.eval := by
    intro t ht
    rw [hz0, hz1, bdi_eq ht, ← sq_norm_eq, hZb ⟨t, ht⟩, norm_polar hρ0, ← ρs_sq]
    exact pow_le_pow_left₀ hρ0 hρ2.le 2
  have hg : z 1 = 0 := by
    have := hz1 0
    simp only [mul_zero, zero_add] at this
    rw [this, hZi 0 (by norm_num)]
    simp [polar, hA.ψ0 (by norm_num)]
  -- closeness
  have hsum : ∑ c ∈ range 30, (z c - (cc c).eval) ^ 2 = ∑ p ∈ range 15, ‖Z p - Cs p‖ ^ 2 := by
    rw [show (30 : ℕ) = 2 * 15 by norm_num, sum_range_two_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [hz0, hz1, sq_norm_eq]
    have e0 : cc (2 * p) = cx p := by simp [cc]
    have e1 : cc (2 * p + 1) = cy p := by
      simp only [cc]; rw [if_neg (by omega), show (2 * p + 1) / 2 = p by omega]
    rw [e0, e1]
    simp [Cs]
  unfold closeOK at hclose
  cases hei : sumOpt ((List.range 5).map (fun j => interiorErr (gI bx j) j)) with
  | none => rw [hei] at hclose; simp at hclose
  | some ei =>
  cases heb : sumOpt ((List.range 10).map (fun w => boundaryErr (win P arcs w) w)) with
  | none => rw [hei, heb] at hclose; simp at hclose
  | some eb =>
  rw [hei, heb] at hclose
  simp only [decide_eq_true_eq] at hclose
  obtain ⟨hei1, hei2⟩ := sumOpt_range hei
  obtain ⟨heb1, heb2⟩ := sumOpt_range heb
  have hint : ∀ j < 5, ‖Z j - Cs j‖ ^ 2 ≤ ((interiorErr (gI bx j) j).getD 0 : ℝ) := by
    intro j hj
    rw [hZi j hj, Cs_interior hj]
    exact interiorErr_sound (hei1 j hj) (hin j (by omega))
  have hbnd : ∀ w < 10, ‖Z (5 + w) - Cs (5 + w)‖ ^ 2 ≤
      ((boundaryErr (win P arcs w) w).getD 0 : ℝ) := by
    intro w hw
    have := hZb ⟨w, hw⟩
    simp only at this
    rw [this, ← polar_add_int ρ _ (mw ⟨w, hw⟩)]
    obtain ⟨hm1, hm2⟩ := hmw ⟨w, hw⟩
    exact boundaryErr_sound hw (heb1 w hw) hρ1 hρ2.le hρ0 hm1 hm2
  have hclose' : ∑ c ∈ range 30, (z c - (cc c).eval) ^ 2 < R2 := by
    rw [hsum, show (15 : ℕ) = 5 + 10 by norm_num, Finset.sum_range_add]
    have h1 : ∑ p ∈ range 5, ‖Z p - Cs p‖ ^ 2 ≤ ∑ j ∈ range 5, ((interiorErr (gI bx j) j).getD 0 : ℝ) :=
      Finset.sum_le_sum (fun j hj => hint j (Finset.mem_range.mp hj))
    have h2 : ∑ w ∈ range 10, ‖Z (5 + w) - Cs (5 + w)‖ ^ 2 ≤
        ∑ w ∈ range 10, ((boundaryErr (win P arcs w) w).getD 0 : ℝ) :=
      Finset.sum_le_sum (fun w hw => hbnd w (Finset.mem_range.mp hw))
    have h3 : ((ei + eb : ℚ) : ℝ) < (survR2 : ℝ) := by exact_mod_cast hclose
    rw [hei2, heb2] at h3
    push_cast at h3
    rw [R2_eq]
    linarith
  -- local uniqueness: `z = c*`, impossible for a boundary point at radius `ρ < ρ*`
  have hu := local_unique contactsOK_true bndOK_true hK hInv gaugeOK_true multPosOK_true weightOK_true
    boundOK_true z hc hb hg hclose'
  have hx := hu 10 (by norm_num)
  have hy := hu 11 (by norm_num)
  rw [show (10 : ℕ) = 2 * 5 by norm_num, hz0] at hx
  rw [show (11 : ℕ) = 2 * 5 + 1 by norm_num, hz1] at hy
  have hcx : cc (2 * 5) = cx 5 := by simp [cc]
  have hcy : cc (2 * 5 + 1) = cy 5 := by simp [cc]
  rw [hcx] at hx
  rw [hcy] at hy
  have hn : ‖Z 5‖ ^ 2 = rho2K.eval := by
    rw [sq_norm_eq, hx, hy, norm_Cs5_sq]
  have hZ5 := hZb ⟨0, by norm_num⟩
  simp only [add_zero] at hZ5
  rw [hZ5, norm_polar hρ0, ← ρs_sq] at hn
  have := ρs_pos
  nlinarith

end CirclePacking
