import CirclePacking.Struct18
import CirclePacking.LocalU

/-!
# Survivors of 18 circles near an isolated rigid structure are impossible below `ρ₁₉`

`iso_impossible18`: no admissible configuration with container parameter `ρ ∈ [ρ₁₉ - epsR, ρ₁₉)` lies in a box
list passing `survIso18` for a structure `T` whose exact points satisfy the local-uniqueness data `L`.  The
boundary circles lie one per window (`surv_assign_gen`); with the labels of `T`
the configuration is within the uniqueness neighbourhood of the exact structure, hence equal to it, whose
boundary circles are at distance `ρ₁₉`, not `ρ`.
-/

open Real Finset

namespace CirclePacking

lemma paramsOK_P18T (k : ℕ) (t : ℤ) : paramsOK (P18T k t) = true := by
  have h : paramsOK (P18 0) = true := by decide +kernel
  exact h

lemma findCentre_spec {k : ℕ} {bx : List IBox} {jc : ℕ} (h : findCentre k bx = some jc) : 1 ≤ jc ∧ jc < k := by
  unfold findCentre at h
  split at h
  next jc' heq =>
    simp only [Option.some.injEq] at h
    subst h
    have hm : jc' ∈ (List.range k).filter (fun j => decide (1 ≤ j) && decide ((gI bx j).shi < S / 2)) := by
      rw [heq]; simp
    simp only [List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hm
    exact ⟨hm.2.1, hm.1⟩
  next => simp at h

lemma labOK_spec {T : Struct18} {k jc : ℕ} (h : labOK T k = true) (h1 : 1 ≤ jc) (hk : jc < k) :
    (∀ i < k, tLab T jc i < k) ∧ (∀ i < k, ∀ j < k, tLab T jc i = tLab T jc j → i = j) := by
  unfold labOK at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not] at h
  rcases h jc hk with h0 | ⟨hb, hi⟩
  · omega
  · refine ⟨hb, fun i hi' j hj' he => ?_⟩
    rcases hi i hi' j hj' with h' | h'
    · exact absurd he h'
    · exact h'

lemma tLab_zero (T : Struct18) (jc : ℕ) : tLab T jc 0 = 0 := by simp [tLab]

set_option maxHeartbeats 4000000 in
/-- **Survivors near an isolated rigid structure are impossible.** -/
theorem iso_impossible18 {k : ℕ} {t : ℤ} (T : Struct18) (L : LUData)
    (hcons : structOK T L k = true) (hok : L.ok = true) (hex : coreExactOK L (structQ T) = true)
    (hnear : coreNearOK23 L (structQ T) = true)
    {ρ : ℝ} (hρ1 : ρ19 - epsR ≤ ρ) (hρ2 : ρ < ρ19) (h2 : 2 ≤ ρ) (hρt : ρ ≤ sc (P18T k t).ρ)
    {s ψ : ℕ → ℝ} {a : Fin (18 - k) → ℝ}
    (hA : AdmR 18 k ρ (fun m => sc ((P18T k t).L m)) s ψ a) {hW : ℤ} {bx : List IBox}
    (hS : survIso18 (P18T k t) hW T bx = true) (hF : Fits (P18T k t) bx s ψ) : False := by
  set P := P18T k t with hPdef
  -- consistency of the structure and the data
  unfold structOK at hcons
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcons
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hTk, hk17⟩, hTB⟩, hLN⟩, hLbnd⟩, hLg⟩, hR2⟩, hc0⟩, ha0⟩, hcc⟩, hlab⟩, -⟩ := hcons
  have hP : paramsOK P = true := paramsOK_P18T k t
  obtain ⟨hρP, -, -, hδ0, hδ1, hδc⟩ := paramsOK_facts hP
  have hAd := AdmR.toAdm (P := P) rfl rfl h2 hρt hA
  have hρ0 : 0 ≤ ρ := by linarith
  obtain ⟨hlen, hin⟩ := hF
  have hPk : P.k = k := rfl
  have hkB : k + (18 - k) = 18 := by omega
  -- unpack the survivor test
  unfold survIso18 at hS
  cases hjc : findCentre T.k bx with
  | none => rw [hjc] at hS; simp at hS
  | some jc =>
  rw [hjc] at hS
  simp only at hS
  obtain ⟨hjc1, hjck⟩ := findCentre_spec hjc
  rw [hTk] at hjck
  cases harcs : survArcsL P bx (nonCentre T.k jc) with
  | none => rw [harcs] at hS; simp at hS
  | some arcs =>
  rw [harcs] at hS
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq, hTk] at hS
  obtain ⟨⟨⟨-, hbad⟩, hwid⟩, hclose⟩ := hS
  unfold survArcsL at harcs
  split_ifs at harcs with hokA
  simp only [Option.some.injEq] at harcs
  simp only [List.all_eq_true] at hokA
  have hall : ∀ b : Fin (18 - k), ∀ p ∈ arcs, Avoids (a b) p := by
    intro b p hp
    rw [← harcs] at hp
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
    have hjk : j < k := by
      simp only [nonCentre, List.mem_filter, List.mem_range, hTk] at hj; exact hj.1
    have hinj : InI (gI bx j) (s j) (ψ j) := hin j (by rw [hlen]; exact hjk)
    exact arc_avoids (hokA j hj) hρP hinj (hAd.s_sq j hjk) (hAd.ib b j hjk)
  have hsep : ∀ b b' : Fin (18 - k), b ≠ b' → ∀ m : ℤ, sc P.δ ≤ |a b - a b' - m| :=
    fun b b' hbb m => sep_of_cos hρP hδ0.le hδ1 hδc (hAd.bb b b' hbb) m
  set win : ℕ → ℤ × ℤ := fun w => (angLo (T.bnd.getD w 0) - hW, angHi (T.bnd.getD w 0) + hW) with hwin
  obtain ⟨σ, hσ, hwinσ⟩ := surv_assign_gen (K := (18 - k)) (by omega) win (jf := P.jf) hδ0
    (fun w hw => hbad w hw) (fun w hw => hwid w hw) (fun b => a b) hsep hall
  choose mw hmw using hwinσ
  -- the labelling: box index `j` carries the structure label `tLab T jc j`
  obtain ⟨hlab1, hlab2⟩ := labOK_spec hlab hjc1 hjck
  let f : Fin k → Fin k := fun j => ⟨tLab T jc j, hlab1 j j.isLt⟩
  have hfinj : Function.Injective f := fun i j h => Fin.ext (hlab2 i i.isLt j j.isLt (congrArg Fin.val h))
  set e := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfinj) with he
  have hf0 : ∀ hk0 : 0 < k, e.symm ⟨0, hk0⟩ = ⟨0, hk0⟩ := by
    intro hk0
    apply e.injective
    rw [Equiv.apply_symm_apply]
    exact Fin.ext (tLab_zero T jc).symm
  -- the configuration in the labels of `T`
  let bang : ℕ → ℝ := fun w => if h : w < (18 - k) then a (σ ⟨w, h⟩) else 0
  let jOf : ℕ → ℕ := fun p => if h : p < k then (e.symm ⟨p, h⟩ : ℕ) else 0
  let Z : ℕ → ℂ := fun p => if p < k then polar (s (jOf p)) (ψ (jOf p)) else polar ρ (bang (p - k))
  let z : ℕ → ℝ := fun c => if c % 2 = 0 then (Z (c / 2)).re else (Z (c / 2)).im
  have hz0 : ∀ p, z (2 * p) = (Z p).re := by
    intro p; simp only [z]; rw [if_pos (by omega), show 2 * p / 2 = p by omega]
  have hz1 : ∀ p, z (2 * p + 1) = (Z p).im := by
    intro p; simp only [z]; rw [if_neg (by omega), show (2 * p + 1) / 2 = p by omega]
  have hjOf : ∀ p (hp : p < k), jOf p < k ∧ tLab T jc (jOf p) = p := by
    intro p hp
    simp only [jOf, dif_pos hp]
    refine ⟨(e.symm ⟨p, hp⟩).isLt, ?_⟩
    have := congrArg Fin.val (e.apply_symm_apply ⟨p, hp⟩)
    exact this
  have hjOf_inj : ∀ p < k, ∀ q < k, jOf p = jOf q → p = q := by
    intro p hp q hq h
    rw [← (hjOf p hp).2, ← (hjOf q hq).2, h]
  have hZi : ∀ p < k, Z p = polar (s (jOf p)) (ψ (jOf p)) := fun p hp => by simp only [Z]; rw [if_pos hp]
  have hZb : ∀ w : Fin (18 - k), Z (k + w) = polar ρ (a (σ w)) := by
    intro w
    simp only [Z, bang]
    rw [if_neg (by omega), dif_pos (by omega)]
    congr 3
    ext; simp
  -- pairwise distances
  have hsep2 : ∀ p < 18, ∀ q < 18, p ≠ q → 4 ≤ ‖Z p - Z q‖ ^ 2 := by
    have hib : ∀ j < k, ∀ w : Fin (18 - k), 4 ≤ ‖polar (s j) (ψ j) - polar ρ (a (σ w))‖ ^ 2 := by
      intro j hj w
      rw [normSq_polar_sub]
      have h := hA.ib (σ w) j hj
      have e' : Real.cos (2 * π * (ψ j - a (σ w))) = Real.cos (2 * π * (a (σ w) - ψ j)) := by
        rw [← Real.cos_neg]; ring_nf
      rw [e']; linarith
    intro p hp q hq hpq
    by_cases hpk : p < k <;> by_cases hqk : q < k
    · rw [hZi p hpk, hZi q hqk, normSq_polar_sub]
      exact hA.ii _ (hjOf p hpk).1 _ (hjOf q hqk).1 (fun h => hpq (hjOf_inj p hpk q hqk h))
    · obtain ⟨w, rfl⟩ : ∃ w : Fin (18 - k), q = k + w := ⟨⟨q - k, by omega⟩, by simp; omega⟩
      rw [hZi p hpk, hZb w]
      exact hib _ (hjOf p hpk).1 w
    · obtain ⟨w, rfl⟩ : ∃ w : Fin (18 - k), p = k + w := ⟨⟨p - k, by omega⟩, by simp; omega⟩
      rw [hZi q hqk, hZb w, norm_sub_rev]
      exact hib _ (hjOf q hqk).1 w
    · obtain ⟨w, rfl⟩ : ∃ w : Fin (18 - k), p = k + w := ⟨⟨p - k, by omega⟩, by simp; omega⟩
      obtain ⟨w', rfl⟩ : ∃ w : Fin (18 - k), q = k + w := ⟨⟨q - k, by omega⟩, by simp; omega⟩
      rw [hZb w, hZb w', normSq_polar_sub]
      have hww : w ≠ w' := by intro h; apply hpq; rw [h]
      have h := hA.bb (σ w) (σ w') (fun h => hww (hσ h))
      linarith
  -- the hypotheses of the local uniqueness theorem
  obtain ⟨-, -, -, hC, -, -, -, -, -, -, -⟩ := LUData.ok_spec hok
  set cs : ℕ → ℝ := coreC (structQ T) with hcsdef
  have hTKB : T.k + T.bnd.length = 18 := by rw [hTk, hTB]; omega
  have hcs : ∀ c < 2 * L.N, |cs c - (L.ctq c : ℝ)| ≤ L.rb := fun c hc => coreC_near23 hnear hc
  have hcon := fun r (hr : r < L.nC) => coreC_contact hex hr
  have hbnd := fun t (ht : t < L.nB) => coreC_bnd hex ht
  have hgc : cs L.gauge = 0 := coreC_gauge hex
  have hLbi : ∀ u < L.nB, L.bi u = k + u := by
    intro u hu
    have hnB : L.nB = (18 - k) := by unfold LUData.nB; rw [hLbnd]; simp
    simp only [LUData.bi, hLbnd]
    rw [List.getD_eq_getElem _ _ (by simp; omega)]
    simp; omega
  have hzc : ∀ r < L.nC, 4 ≤ (z (2 * L.ci r) - z (2 * L.cj r)) ^ 2 +
      (z (2 * L.ci r + 1) - z (2 * L.cj r + 1)) ^ 2 := by
    intro r hr
    obtain ⟨hi, hj, hij⟩ := hC r hr
    rw [hLN] at hi hj
    rw [hz0, hz0, hz1, hz1]
    have := hsep2 _ hi _ hj hij
    rw [sq_norm_eq] at this
    simpa using this
  have hzb : ∀ u < L.nB, z (2 * L.bi u) ^ 2 + z (2 * L.bi u + 1) ^ 2 ≤ 8 + 4 * √3 := by
    intro u hu
    have hnB : L.nB = (18 - k) := by unfold LUData.nB; rw [hLbnd]; simp
    rw [hLbi u hu, hz0, hz1, ← sq_norm_eq, hZb ⟨u, by omega⟩, norm_polar hρ0, ← ρ19_sq]
    exact pow_le_pow_left₀ hρ0 hρ2.le 2
  have hzg : z L.gauge = 0 := by
    rw [hLg]
    have h1 := hz1 0
    simp only [mul_zero, zero_add] at h1
    rw [h1, hZi 0 (by omega)]
    have hj0 : jOf 0 = 0 := by
      simp only [jOf, dif_pos (show 0 < k by omega)]
      rw [hf0 (by omega)]
    rw [hj0]
    simp [polar, hA.ψ0 (by omega)]
  -- closeness
  have hsum : ∑ c ∈ range (2 * L.N), (z c - cs c) ^ 2 = ∑ p ∈ range 18, ‖Z p - structC T p‖ ^ 2 := by
    rw [hLN, sum_two_mul]
    apply Finset.sum_congr rfl
    intro p hp
    have hp' : p < T.k + T.bnd.length := by rw [hTKB]; exact mem_range.mp hp
    obtain ⟨e1, e2⟩ := coreC_structQ T hp'
    rw [hz0, hz1, hcsdef, e1, e2, sq_norm_eq]
    simp
  cases hei : eiOf18 T jc bx with
  | none => rw [hei] at hclose; simp at hclose
  | some ei =>
  cases heb : sumOpt ((List.range (18 - k)).map (fun w => boundaryErrG (win w) (angLo (T.bnd.getD w 0))
      (angHi (T.bnd.getD w 0)))) with
  | none => simp only [hei, hwin] at hclose; rw [heb] at hclose; simp at hclose
  | some eb =>
  simp only [hei, hwin] at hclose
  rw [heb] at hclose
  simp only [decide_eq_true_eq] at hclose
  unfold eiOf18 at hei
  rw [hTk] at hei
  obtain ⟨hei1, hei2⟩ := sumOpt_range hei
  obtain ⟨heb1, heb2⟩ := sumOpt_range heb
  -- interior points: through the labelling
  have hint : ∀ j < k, ‖Z (tLab T jc j) - structC T (tLab T jc j)‖ ^ 2 ≤
      ((interiorErrG (gI bx j) (radLo (T.code (tLab T jc j))) (radHi (T.code (tLab T jc j)))
        (angLo (T.ang (tLab T jc j))) (angHi (T.ang (tLab T jc j)))).getD 0 : ℝ) := by
    intro j hj
    have hp := hlab1 j hj
    have hjj : jOf (tLab T jc j) = j := hlab2 _ (hjOf _ hp).1 j hj (hjOf _ hp).2
    rw [hZi _ hp, hjj, structC_int T (by rw [hTk]; exact hp)]
    exact interiorErrG_sound (hei1 j hj) (hin j (by rw [hlen]; exact hj)) (radLo_le _) (le_radHi _)
      (angLo_le _) (le_angHi _)
  have hsumI : ∑ p ∈ range k, ‖Z p - structC T p‖ ^ 2 ≤ (ei : ℝ) := by
    have hreidx : ∑ p ∈ range k, ‖Z p - structC T p‖ ^ 2 =
        ∑ j ∈ range k, ‖Z (tLab T jc j) - structC T (tLab T jc j)‖ ^ 2 := by
      rw [← Fin.sum_univ_eq_sum_range (fun p => ‖Z p - structC T p‖ ^ 2) k,
        ← Fin.sum_univ_eq_sum_range (fun j => ‖Z (tLab T jc j) - structC T (tLab T jc j)‖ ^ 2) k]
      exact (Equiv.sum_comp e (fun p : Fin k => ‖Z p - structC T p‖ ^ 2)).symm
    rw [hreidx, hei2]
    push_cast
    exact Finset.sum_le_sum (fun j hj => hint j (mem_range.mp hj))
  -- boundary circles: through the windows
  have hsumB : ∑ w ∈ range (18 - k), ‖Z (k + w) - structC T (k + w)‖ ^ 2 ≤ (eb : ℝ) := by
    rw [heb2]
    push_cast
    apply Finset.sum_le_sum
    intro w hw
    have hw' := mem_range.mp hw
    have hZ := hZb ⟨w, hw'⟩
    simp only at hZ
    rw [hZ, ← polar_add_int ρ _ (mw ⟨w, hw'⟩), structC_bnd T (by rw [hTk]; omega)]
    have hkk : k + w - T.k = w := by rw [hTk]; omega
    rw [hkk]
    obtain ⟨hy1, hy2⟩ := hmw ⟨w, hw'⟩
    exact boundaryErrG_sound (heb1 w hw') ρ19_pos ρ19_sq_le hρ1 hρ2.le hρ0 hy1 hy2 (angLo_le _) (le_angHi _)
  have hclose' : ∑ c ∈ range (2 * L.N), (z c - cs c) ^ 2 < L.R2 := by
    rw [hsum, show (18 : ℕ) = k + (18 - k) by omega, Finset.sum_range_add]
    have hR2' : ((T.R2 : ℚ) : ℝ) ≤ ((L.R2 : ℚ) : ℝ) := by exact_mod_cast hR2
    have hcl : ((ei + eb : ℚ) : ℝ) < ((T.R2 : ℚ) : ℝ) := by exact_mod_cast hclose
    push_cast at hcl
    linarith
  -- local uniqueness: `z = c*`, impossible for a boundary circle at radius `ρ < ρ₁₉`
  have hu := local_unique_gen L hok cs z (8 + 4 * √3) hcs hcon hbnd hgc hzc hzb hzg hclose'
  have hk1 : 0 < L.nB := by unfold LUData.nB; rw [hLbnd]; simp; omega
  have hb0 := hLbi 0 hk1
  simp only [add_zero] at hb0
  have hx := hu (2 * L.bi 0) (by rw [hb0, hLN]; omega)
  have hy := hu (2 * L.bi 0 + 1) (by rw [hb0, hLN]; omega)
  have hcb : cs (2 * L.bi 0) ^ 2 + cs (2 * L.bi 0 + 1) ^ 2 = 8 + 4 * √3 := hbnd 0 hk1
  rw [← hx, ← hy, hb0, hz0, hz1, ← sq_norm_eq] at hcb
  have hZk := hZb ⟨0, by omega⟩
  simp only [add_zero] at hZk
  rw [hZk, norm_polar hρ0, ← ρ19_sq] at hcb
  have := (sq_eq_sq₀ hρ0 ρ19_pos.le).mp hcb
  linarith

end CirclePacking
