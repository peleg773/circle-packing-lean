import CirclePacking.Surv16
import CirclePacking.CStar16

/-!
# The record case of 16 circles (`k = 5`)

No admissible configuration with 5 interior circles and container parameter `ρ ∈ [ρ* - epsR, ρ*)` lies in
a box list passing `survOK16`: such a configuration would be within the uniqueness neighbourhood of `c*`,
hence equal to `c*`, whose boundary circles are at distance `ρ*`, not `ρ`.
-/

open Real Finset

namespace CirclePacking

set_option maxRecDepth 100000 in
theorem n16LU_ok : n16LU.ok = true := by decide +kernel

theorem paramsOK_P16_5 : paramsOK (P16 5) = true := by decide +kernel

lemma n16LU_ctq {c : ℕ} (hc : c < 32) : n16LU.ctq c = n16K.utq c := by
  simp only [LUData.ctq, KData.utq, n16LU, n16K, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hc]

lemma n16LU_bi {t : ℕ} (ht : t < 11) : n16LU.bi t = 5 + t := by
  have : ∀ t < 11, n16LU.bi t = 5 + t := by decide
  exact this t ht

set_option maxHeartbeats 1000000 in
theorem k5_impossible16
    {ρ : ℝ} (hρ1 : ρ16 - epsR ≤ ρ) (hρ2 : ρ < ρ16) (h2 : 2 ≤ ρ) (hρt : ρ ≤ sc (P16 5).ρ)
    {s ψ : ℕ → ℝ} {a : Fin (16 - 5) → ℝ}
    (hA : AdmR 16 5 ρ (fun m => sc ((P16 5).L m)) s ψ a) {bx : List IBox}
    (hS : survOK16 (P16 5) bx = true) (hF : Fits (P16 5) bx s ψ) : False := by
  set P := P16 5 with hPdef
  have hP : paramsOK P = true := paramsOK_P16_5
  obtain ⟨hρP, -, -, hδ0, hδ1, hδc⟩ := paramsOK_facts hP
  have hAd := AdmR.toAdm (P := P) rfl rfl h2 hρt hA
  have hρ0 : 0 ≤ ρ := by linarith
  obtain ⟨hlen, hin⟩ := hF
  -- unpack `survOK16`
  unfold survOK16 at hS
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
  have hall : ∀ b : Fin 11, ∀ p ∈ arcs, Avoids (a b) p := by
    intro b p hp
    rw [← harcs] at hp
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
    have hj5 := List.mem_range.mp hj
    have hinj : InI (gI bx j) (s j) (ψ j) := hin j (by rw [hlen]; exact hj5)
    exact arc_avoids (hok j hj5) hρP hinj (hAd.s_sq j hj5) (hAd.ib b j hj5)
  have hsep : ∀ b b' : Fin 11, b ≠ b' → ∀ m : ℤ, sc P.δ ≤ |a b - a b' - m| :=
    fun b b' hbb m => sep_of_cos hρP hδ0.le hδ1 hδc (hAd.bb b b' hbb) m
  obtain ⟨σ, hσ, hwin⟩ := surv_assign16 (jf := P.jf) hδ0 (fun w hw => hbad w hw) (fun w hw => hwid w hw)
    (fun b => a b) hsep hall
  choose mw hmw using hwin
  -- the configuration in the labelling of `c*`
  let bang : ℕ → ℝ := fun w => if h : w < 11 then a (σ ⟨w, h⟩) else 0
  let Z : ℕ → ℂ := fun p => if p < 5 then polar (s p) (ψ p) else polar ρ (bang (p - 5))
  let z : ℕ → ℝ := fun c => if c % 2 = 0 then (Z (c / 2)).re else (Z (c / 2)).im
  have hz0 : ∀ p, z (2 * p) = (Z p).re := by
    intro p; simp only [z]; rw [if_pos (by omega), show 2 * p / 2 = p by omega]
  have hz1 : ∀ p, z (2 * p + 1) = (Z p).im := by
    intro p; simp only [z]; rw [if_neg (by omega), show (2 * p + 1) / 2 = p by omega]
  have hZi : ∀ p < 5, Z p = polar (s p) (ψ p) := fun p hp => by simp only [Z]; rw [if_pos hp]
  have hZb : ∀ w : Fin 11, Z (5 + w) = polar ρ (a (σ w)) := by
    intro w
    simp only [Z, bang]
    rw [if_neg (by omega), dif_pos (by omega)]
    congr 3
    ext; simp
  -- pairwise distances
  have hsep2 : ∀ p < 16, ∀ q < 16, p ≠ q → 4 ≤ ‖Z p - Z q‖ ^ 2 := by
    have hib : ∀ j < 5, ∀ w : Fin 11, 4 ≤ ‖polar (s j) (ψ j) - polar ρ (a (σ w))‖ ^ 2 := by
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
    · obtain ⟨w, rfl⟩ : ∃ w : Fin 11, q = 5 + w := ⟨⟨q - 5, by omega⟩, by simp; omega⟩
      rw [hZi p hp5, hZb w]
      exact hib p hp5 w
    · obtain ⟨w, rfl⟩ : ∃ w : Fin 11, p = 5 + w := ⟨⟨p - 5, by omega⟩, by simp; omega⟩
      rw [hZi q hq5, hZb w, norm_sub_rev]
      exact hib q hq5 w
    · obtain ⟨w, rfl⟩ : ∃ w : Fin 11, p = 5 + w := ⟨⟨p - 5, by omega⟩, by simp; omega⟩
      obtain ⟨w', rfl⟩ : ∃ w : Fin 11, q = 5 + w := ⟨⟨q - 5, by omega⟩, by simp; omega⟩
      rw [hZb w, hZb w', normSq_polar_sub]
      have hww : w ≠ w' := by intro h; apply hpq; rw [h]
      have h := hA.bb (σ w) (σ w') (fun h => hww (hσ h))
      linarith
  -- the hypotheses of the local uniqueness theorem
  have hcs : ∀ c < 2 * n16LU.N, |u16 c - (n16LU.ctq c : ℝ)| ≤ n16LU.rb := by
    intro c hc
    have hc' : c < 32 := hc
    rw [n16LU_ctq hc']
    exact u16_near (by omega)
  have hcon : ∀ r < n16LU.nC, (u16 (2 * n16LU.ci r) - u16 (2 * n16LU.cj r)) ^ 2 +
      (u16 (2 * n16LU.ci r + 1) - u16 (2 * n16LU.cj r + 1)) ^ 2 = 4 :=
    fun r hr => C16_contact (r := r) hr
  have hbnd : ∀ t < n16LU.nB, u16 (2 * n16LU.bi t) ^ 2 + u16 (2 * n16LU.bi t + 1) ^ 2 = P16s :=
    fun t ht => C16_bnd (t := t) ht
  have hgc : u16 n16LU.gauge = 0 := C16_gauge
  have hzc : ∀ r < n16LU.nC, 4 ≤ (z (2 * n16LU.ci r) - z (2 * n16LU.cj r)) ^ 2 +
      (z (2 * n16LU.ci r + 1) - z (2 * n16LU.cj r + 1)) ^ 2 := by
    intro r hr
    have hcij : n16LU.ci r < 16 ∧ n16LU.cj r < 16 ∧ n16LU.ci r ≠ n16LU.cj r := by
      have : ∀ r < 21, n16LU.ci r < 16 ∧ n16LU.cj r < 16 ∧ n16LU.ci r ≠ n16LU.cj r := by decide
      exact this r hr
    obtain ⟨hi, hj, hij⟩ := hcij
    rw [hz0, hz0, hz1, hz1]
    have := hsep2 _ hi _ hj hij
    rw [sq_norm_eq] at this
    simpa using this
  have hzb : ∀ t < n16LU.nB, z (2 * n16LU.bi t) ^ 2 + z (2 * n16LU.bi t + 1) ^ 2 ≤ P16s := by
    intro t ht
    have ht' : t < 11 := ht
    rw [hz0, hz1, n16LU_bi ht', ← sq_norm_eq, hZb ⟨t, ht'⟩, norm_polar hρ0, ← ρ16_sq]
    exact pow_le_pow_left₀ hρ0 hρ2.le 2
  have hzg : z n16LU.gauge = 0 := by
    have := hz1 0
    simp only [mul_zero, zero_add] at this
    show z 1 = 0
    rw [this, hZi 0 (by norm_num)]
    simp [polar, hA.ψ0 (by norm_num)]
  -- closeness
  have hsum : ∑ c ∈ range (2 * n16LU.N), (z c - u16 c) ^ 2 = ∑ p ∈ range 16, ‖Z p - C16 p‖ ^ 2 := by
    rw [show 2 * n16LU.N = 2 * 16 from rfl, sum_two_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [hz0, hz1, sq_norm_eq]
    simp [C16]
  unfold closeOK16 at hclose
  cases hei : sumOpt ((List.range 5).map (fun j => interiorErr16 (gI bx j) j)) with
  | none => rw [hei] at hclose; simp at hclose
  | some ei =>
  cases heb : sumOpt ((List.range 11).map (fun w => boundaryErr16 (win16 w) w)) with
  | none => rw [hei, heb] at hclose; simp at hclose
  | some eb =>
  rw [hei, heb] at hclose
  simp only [decide_eq_true_eq] at hclose
  obtain ⟨hei1, hei2⟩ := sumOpt_range hei
  obtain ⟨heb1, heb2⟩ := sumOpt_range heb
  have hint : ∀ j < 5, ‖Z j - C16 j‖ ^ 2 ≤ ((interiorErr16 (gI bx j) j).getD 0 : ℝ) := by
    intro j hj
    obtain ⟨m, hm1, hm2⟩ := C16_angle (p := j) (by omega)
    obtain ⟨hr1, hr2⟩ := C16_radius (p := j) (by omega)
    have hpol : C16 j = polar ‖C16 j‖ (toTurn (C16 j) + m) := by
      rw [polar_add_int]; exact (polar_toTurn _).symm
    rw [hZi j hj, hpol]
    exact interiorErr16_sound (hei1 j hj) (hin j (by rw [hlen]; exact hj)) hr1 hr2 hm1.le hm2.le
  have hbnd' : ∀ w < 11, ‖Z (5 + w) - C16 (5 + w)‖ ^ 2 ≤
      ((boundaryErr16 (win16 w) w).getD 0 : ℝ) := by
    intro w hw
    obtain ⟨m, hm1, hm2⟩ := C16_angle (p := 5 + w) (by omega)
    have hpol : C16 (5 + w) = polar ρ16 (toTurn (C16 (5 + w)) + m) := by
      rw [polar_add_int, ← C16_bnd_norm hw]; exact (polar_toTurn _).symm
    have := hZb ⟨w, hw⟩
    simp only at this
    rw [this, ← polar_add_int ρ _ (mw ⟨w, hw⟩), hpol]
    obtain ⟨hy1, hy2⟩ := hmw ⟨w, hw⟩
    exact boundaryErr16_sound (heb1 w hw) ρ16_pos ρ16_sq_le hρ1 hρ2.le hρ0 hy1 hy2 hm1.le hm2.le
  have hclose' : ∑ c ∈ range (2 * n16LU.N), (z c - u16 c) ^ 2 < n16LU.R2 := by
    rw [hsum, show (16 : ℕ) = 5 + 11 by norm_num, Finset.sum_range_add]
    have h1 : ∑ p ∈ range 5, ‖Z p - C16 p‖ ^ 2 ≤ ∑ j ∈ range 5, ((interiorErr16 (gI bx j) j).getD 0 : ℝ) :=
      Finset.sum_le_sum (fun j hj => hint j (Finset.mem_range.mp hj))
    have h2 : ∑ w ∈ range 11, ‖Z (5 + w) - C16 (5 + w)‖ ^ 2 ≤
        ∑ w ∈ range 11, ((boundaryErr16 (win16 w) w).getD 0 : ℝ) :=
      Finset.sum_le_sum (fun w hw => hbnd' w (Finset.mem_range.mp hw))
    have h3 : ((ei + eb : ℚ) : ℝ) < (survR2_16 : ℝ) := by exact_mod_cast hclose
    rw [hei2, heb2] at h3
    push_cast at h3
    have hR' : n16LU.R2 = survR2_16 := by decide +kernel
    have hR : (n16LU.R2 : ℝ) = (survR2_16 : ℝ) := by rw [hR']
    rw [hR]
    linarith
  -- local uniqueness: `z = c*`, impossible for a boundary point at radius `ρ < ρ*`
  have hu := local_unique_gen n16LU n16LU_ok u16 z P16s hcs hcon hbnd hgc hzc hzb hzg hclose'
  have hx := hu 10 (by decide)
  have hy := hu 11 (by decide)
  rw [show (10 : ℕ) = 2 * 5 by norm_num, hz0] at hx
  rw [show (11 : ℕ) = 2 * 5 + 1 by norm_num, hz1] at hy
  have hn : ‖Z 5‖ = ‖C16 5‖ := by
    congr 1
    apply Complex.ext
    · rw [hx]; rfl
    · rw [hy]; rfl
  have hZ5 := hZb ⟨0, by norm_num⟩
  simp only [add_zero] at hZ5
  rw [hZ5, norm_polar hρ0, show (5 : ℕ) = 5 + 0 from rfl, C16_bnd_norm (t := 0) (by norm_num)] at hn
  linarith

end CirclePacking
