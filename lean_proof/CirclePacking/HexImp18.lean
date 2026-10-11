import CirclePacking.Iso18
import CirclePacking.HexCore18

/-!
# Survivors of 18 circles near the hexagon are impossible below `ρ₁₉`

`hex_impossible18`: no admissible configuration with seven interior circles and container parameter
`ρ ∈ [ρ₁₉ - epsR, ρ₁₉)` lies in a box list passing `survHex18`.  The boundary circles fill the six windows between
the ring arcs two by two, except one window (`m0`) holding a single circle (`surv_assign_hex`); the hexagon, the
centre and the ten pinned boundary circles are then within the uniqueness neighbourhood of the core `hexLU m0`,
hence equal to it, whose boundary circles are at distance `ρ₁₉`, not `ρ`.
-/

open Real Finset

namespace CirclePacking

set_option maxHeartbeats 4000000 in
/-- **Survivors near the hexagon are impossible.** -/
theorem hex_impossible18 {t : ℤ}
    {ρ : ℝ} (hρ1 : ρ19 - epsR ≤ ρ) (hρ2 : ρ < ρ19) (h2 : 2 ≤ ρ) (hρt : ρ ≤ sc (P18T 7 t).ρ)
    {s ψ : ℕ → ℝ} {a : Fin (18 - 7) → ℝ}
    (hA : AdmR 18 7 ρ (fun m => sc ((P18T 7 t).L m)) s ψ a) {hW : ℤ} {bx : List IBox}
    (hS : survHex18 (P18T 7 t) hW sHex hexR2s bx = true) (hF : Fits (P18T 7 t) bx s ψ) : False := by
  set P := P18T 7 t with hPdef
  obtain ⟨hTk, hlab, hc0, ha0, hcc, hTB⟩ := sHex_shape
  have hP : paramsOK P = true := paramsOK_P18T 7 t
  obtain ⟨hρP, -, -, hδ0, hδ1, hδc⟩ := paramsOK_facts hP
  have hAd := AdmR.toAdm (P := P) rfl rfl h2 hρt hA
  have hρ0 : 0 ≤ ρ := by linarith
  obtain ⟨hlen, hin⟩ := hF
  -- unpack the survivor test
  unfold survHex18 at hS
  cases hjc : findCentre sHex.k bx with
  | none => rw [hjc] at hS; simp at hS
  | some jc =>
  rw [hjc] at hS
  simp only at hS
  obtain ⟨hjc1, hjck⟩ := findCentre_spec hjc
  rw [hTk] at hjck
  cases harcs : survArcsL P bx (nonCentre sHex.k jc) with
  | none => rw [harcs] at hS; simp at hS
  | some arcs =>
  rw [harcs] at hS
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hS
  obtain ⟨⟨hgap, hwid⟩, hclose⟩ := hS
  unfold survArcsL at harcs
  split_ifs at harcs with hokA
  simp only [Option.some.injEq] at harcs
  simp only [List.all_eq_true] at hokA
  have hall : ∀ b : Fin (18 - 7), ∀ p ∈ arcs, Avoids (a b) p := by
    intro b p hp
    rw [← harcs] at hp
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
    have hjk : j < 7 := by
      simp only [nonCentre, List.mem_filter, List.mem_range, hTk] at hj; exact hj.1
    have hinj : InI (gI bx j) (s j) (ψ j) := hin j (by rw [hlen]; exact hjk)
    exact arc_avoids (hokA j hj) hρP hinj (hAd.s_sq j hjk) (hAd.ib b j hjk)
  have hsep : ∀ b b' : Fin (18 - 7), b ≠ b' → ∀ m : ℤ, sc P.δ ≤ |a b - a b' - m| :=
    fun b b' hbb m => sep_of_cos hρP hδ0.le hδ1 hδc (hAd.bb b b' hbb) m
  set win : ℕ → ℤ × ℤ := fun w =>
    (angLo (sHex.bnd.getD (2 * w) 0) - hW, angHi (sHex.bnd.getD (2 * w + 1) 0) + hW) with hwin
  obtain ⟨m0, τ, hτ, hτb⟩ := surv_assign_hex win hδ0 (fun w hw => hgap w hw) (fun w hw => hwid w hw)
    (fun b => a b) hsep hall
  choose mw hmw using hτb
  -- the labelling of the interior circles
  obtain ⟨hlab1, hlab2⟩ := labOK_spec hlab hjc1 hjck
  let f : Fin 7 → Fin 7 := fun j => ⟨tLab sHex jc j, hlab1 j j.isLt⟩
  have hfinj : Function.Injective f := fun i j h => Fin.ext (hlab2 i i.isLt j j.isLt (congrArg Fin.val h))
  set e := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfinj) with he
  have hf0 : e.symm ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩ := by
    apply e.injective
    rw [Equiv.apply_symm_apply]
    exact Fin.ext (tLab_zero sHex jc).symm
  -- the configuration in the labels of the core `hexLU m0`
  let bang : ℕ → ℝ := fun s' => if h : s' < 10 then a (τ ⟨s', h⟩) else 0
  let jOf : ℕ → ℕ := fun p => if h : p < 7 then (e.symm ⟨p, h⟩ : ℕ) else 0
  let Z : ℕ → ℂ := fun p => if p < 7 then polar (s (jOf p)) (ψ (jOf p)) else polar ρ (bang (p - 7))
  let z : ℕ → ℝ := fun c => if c % 2 = 0 then (Z (c / 2)).re else (Z (c / 2)).im
  have hz0 : ∀ p, z (2 * p) = (Z p).re := by
    intro p; simp only [z]; rw [if_pos (by omega), show 2 * p / 2 = p by omega]
  have hz1 : ∀ p, z (2 * p + 1) = (Z p).im := by
    intro p; simp only [z]; rw [if_neg (by omega), show (2 * p + 1) / 2 = p by omega]
  have hjOf : ∀ p (hp : p < 7), jOf p < 7 ∧ tLab sHex jc (jOf p) = p := by
    intro p hp
    simp only [jOf, dif_pos hp]
    refine ⟨(e.symm ⟨p, hp⟩).isLt, ?_⟩
    have := congrArg Fin.val (e.apply_symm_apply ⟨p, hp⟩)
    exact this
  have hjOf_inj : ∀ p < 7, ∀ q < 7, jOf p = jOf q → p = q := by
    intro p hp q hq h
    rw [← (hjOf p hp).2, ← (hjOf q hq).2, h]
  have hZi : ∀ p < 7, Z p = polar (s (jOf p)) (ψ (jOf p)) := fun p hp => by simp only [Z]; rw [if_pos hp]
  have hZb : ∀ s' : Fin 10, Z (7 + s') = polar ρ (a (τ s')) := by
    intro s'
    simp only [Z, bang]
    rw [if_neg (by omega), dif_pos (by omega)]
    congr 3
    ext; simp
  -- pairwise distances
  have hsep2 : ∀ p < 17, ∀ q < 17, p ≠ q → 4 ≤ ‖Z p - Z q‖ ^ 2 := by
    have hib : ∀ j < 7, ∀ w : Fin (18 - 7), 4 ≤ ‖polar (s j) (ψ j) - polar ρ (a w)‖ ^ 2 := by
      intro j hj w
      rw [normSq_polar_sub]
      have h := hA.ib w j hj
      have e' : Real.cos (2 * π * (ψ j - a w)) = Real.cos (2 * π * (a w - ψ j)) := by
        rw [← Real.cos_neg]; ring_nf
      rw [e']; linarith
    intro p hp q hq hpq
    by_cases hpk : p < 7 <;> by_cases hqk : q < 7
    · rw [hZi p hpk, hZi q hqk, normSq_polar_sub]
      exact hA.ii _ (hjOf p hpk).1 _ (hjOf q hqk).1 (fun h => hpq (hjOf_inj p hpk q hqk h))
    · obtain ⟨w, rfl⟩ : ∃ w : Fin 10, q = 7 + w := ⟨⟨q - 7, by omega⟩, by simp; omega⟩
      rw [hZi p hpk, hZb w]
      exact hib _ (hjOf p hpk).1 (τ w)
    · obtain ⟨w, rfl⟩ : ∃ w : Fin 10, p = 7 + w := ⟨⟨p - 7, by omega⟩, by simp; omega⟩
      rw [hZi q hqk, hZb w, norm_sub_rev]
      exact hib _ (hjOf q hqk).1 (τ w)
    · obtain ⟨w, rfl⟩ : ∃ w : Fin 10, p = 7 + w := ⟨⟨p - 7, by omega⟩, by simp; omega⟩
      obtain ⟨w', rfl⟩ : ∃ w : Fin 10, q = 7 + w := ⟨⟨q - 7, by omega⟩, by simp; omega⟩
      rw [hZb w, hZb w', normSq_polar_sub]
      have hww : w ≠ w' := by intro h; apply hpq; rw [h]
      have h := hA.bb (τ w) (τ w') (fun h => hww (hτ h))
      linarith
  -- the core with short window `m0`
  have hm06 : (m0 : ℕ) < 6 := m0.isLt
  set L := hexLU m0 with hLdef
  have hok : L.ok = true := hexLU_ok m0 hm06
  obtain ⟨hLN, hLbnd, hLg, hR2⟩ := hexLU_shape m0 hm06
  have hex : coreExactOK L (hexQg m0) = true := hexG_exact m0 hm06
  have hnear : coreNearOK23 L (hexQg m0) = true := hexG_near m0 hm06
  obtain ⟨-, -, -, hC, -, -, -, -, -, -, -⟩ := LUData.ok_spec hok
  set cs : ℕ → ℝ := coreC (hexQg m0) with hcsdef
  have hcs : ∀ c < 2 * L.N, |cs c - (L.ctq c : ℝ)| ≤ L.rb := fun c hc => coreC_near23 hnear hc
  have hcon := fun r (hr : r < L.nC) => coreC_contact hex hr
  have hbnd := fun u (hu : u < L.nB) => coreC_bnd hex hu
  have hgc : cs L.gauge = 0 := coreC_gauge hex
  have hnB : L.nB = 10 := by unfold LUData.nB; rw [hLbnd]; rfl
  have hLbi : ∀ u < L.nB, L.bi u = 7 + u := by
    intro u hu
    rw [hnB] at hu
    show L.bnd.getD u 0 = 7 + u
    rw [hLbnd]
    interval_cases u <;> rfl
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
    rw [hLbi u hu, hz0, hz1, ← sq_norm_eq, hZb ⟨u, by omega⟩, norm_polar hρ0, ← ρ19_sq]
    exact pow_le_pow_left₀ hρ0 hρ2.le 2
  have hzg : z L.gauge = 0 := by
    rw [hLg]
    have h1 := hz1 0
    simp only [mul_zero, zero_add] at h1
    rw [h1, hZi 0 (by omega)]
    have hj0 : jOf 0 = 0 := by
      simp only [jOf, dif_pos (show 0 < 7 by omega)]
      rw [hf0]
    rw [hj0]
    simp [polar, hA.ψ0 (by omega)]
  -- closeness
  have hsum : ∑ c ∈ range (2 * L.N), (z c - cs c) ^ 2 = ∑ p ∈ range 17, ‖Z p - hexC m0 p‖ ^ 2 := by
    rw [hLN, sum_two_mul]
    apply Finset.sum_congr rfl
    intro p hp
    obtain ⟨e1, e2⟩ := coreC_hexQg m0 (mem_range.mp hp)
    rw [hz0, hz1, hcsdef, e1, e2, sq_norm_eq]
    simp
  cases hei : eiOf18 sHex jc bx with
  | none => rw [hei] at hclose; simp at hclose
  | some ei =>
  rw [hei] at hclose
  simp only [List.all_eq_true, List.mem_range] at hclose
  have hcm := hclose m0 hm06
  cases heb : sumOpt ((List.range 10).map (fun s' =>
      boundaryErrG (hexSlotLo win P.δ m0 s', hexSlotHi win P.δ m0 s')
        (angLo (sHex.bnd.getD (2 * hexWin m0 (s' / 2) + s' % 2) 0))
        (angHi (sHex.bnd.getD (2 * hexWin m0 (s' / 2) + s' % 2) 0)))) with
  | none => simp only [hwin] at hcm; rw [heb] at hcm; simp at hcm
  | some eb =>
  simp only [hwin] at hcm
  rw [heb] at hcm
  simp only [decide_eq_true_eq] at hcm
  unfold eiOf18 at hei
  rw [hTk] at hei
  obtain ⟨hei1, hei2⟩ := sumOpt_range hei
  obtain ⟨heb1, heb2⟩ := sumOpt_range heb
  have hint : ∀ j < 7, ‖Z (tLab sHex jc j) - hexC m0 (tLab sHex jc j)‖ ^ 2 ≤
      ((interiorErrG (gI bx j) (radLo (sHex.code (tLab sHex jc j))) (radHi (sHex.code (tLab sHex jc j)))
        (angLo (sHex.ang (tLab sHex jc j))) (angHi (sHex.ang (tLab sHex jc j)))).getD 0 : ℝ) := by
    intro j hj
    have hp := hlab1 j hj
    have hjj : jOf (tLab sHex jc j) = j := hlab2 _ (hjOf _ hp).1 j hj (hjOf _ hp).2
    rw [hZi _ hp, hjj, hexC_int m0 hp]
    exact interiorErrG_sound (hei1 j hj) (hin j (by rw [hlen]; exact hj)) (radLo_le _) (le_radHi _)
      (angLo_le _) (le_angHi _)
  have hsumI : ∑ p ∈ range 7, ‖Z p - hexC m0 p‖ ^ 2 ≤ (ei : ℝ) := by
    have hreidx : ∑ p ∈ range 7, ‖Z p - hexC m0 p‖ ^ 2 =
        ∑ j ∈ range 7, ‖Z (tLab sHex jc j) - hexC m0 (tLab sHex jc j)‖ ^ 2 := by
      rw [← Fin.sum_univ_eq_sum_range (fun p => ‖Z p - hexC m0 p‖ ^ 2) 7,
        ← Fin.sum_univ_eq_sum_range (fun j => ‖Z (tLab sHex jc j) - hexC m0 (tLab sHex jc j)‖ ^ 2) 7]
      exact (Equiv.sum_comp e (fun p : Fin 7 => ‖Z p - hexC m0 p‖ ^ 2)).symm
    rw [hreidx, hei2]
    push_cast
    exact Finset.sum_le_sum (fun j hj => hint j (mem_range.mp hj))
  have hsumB : ∑ s' ∈ range 10, ‖Z (7 + s') - hexC m0 (7 + s')‖ ^ 2 ≤ (eb : ℝ) := by
    rw [heb2]
    push_cast
    apply Finset.sum_le_sum
    intro s' hs
    have hs' := mem_range.mp hs
    have hZ := hZb ⟨s', hs'⟩
    simp only at hZ
    rw [hZ, ← polar_add_int ρ _ (mw ⟨s', hs'⟩), hexC_bnd m0 s']
    obtain ⟨hy1, hy2⟩ := hmw ⟨s', hs'⟩
    exact boundaryErrG_sound (heb1 s' hs') ρ19_pos ρ19_sq_le hρ1 hρ2.le hρ0 hy1 hy2 (angLo_le _) (le_angHi _)
  have hclose' : ∑ c ∈ range (2 * L.N), (z c - cs c) ^ 2 < L.R2 := by
    rw [hsum, show (17 : ℕ) = 7 + 10 by norm_num, Finset.sum_range_add]
    have hR2' : ((hexR2s.getD m0 0 : ℚ) : ℝ) ≤ ((L.R2 : ℚ) : ℝ) := by exact_mod_cast hR2
    have hcl : ((ei + eb : ℚ) : ℝ) < ((hexR2s.getD m0 0 : ℚ) : ℝ) := by exact_mod_cast hcm
    push_cast at hcl
    linarith
  -- local uniqueness: `z = c*`, impossible for a boundary circle at radius `ρ < ρ₁₉`
  have hu := local_unique_gen L hok cs z (8 + 4 * √3) hcs hcon hbnd hgc hzc hzb hzg hclose'
  have hk1 : 0 < L.nB := by rw [hnB]; norm_num
  have hb0 := hLbi 0 hk1
  simp only [add_zero] at hb0
  have hx := hu (2 * L.bi 0) (by rw [hb0, hLN]; norm_num)
  have hy := hu (2 * L.bi 0 + 1) (by rw [hb0, hLN]; norm_num)
  have hcb : cs (2 * L.bi 0) ^ 2 + cs (2 * L.bi 0 + 1) ^ 2 = 8 + 4 * √3 := hbnd 0 hk1
  rw [← hx, ← hy, hb0, hz0, hz1, ← sq_norm_eq] at hcb
  have hZk := hZb ⟨0, by norm_num⟩
  simp only [add_zero] at hZk
  rw [hZk, norm_polar hρ0, ← ρ19_sq] at hcb
  have := (sq_eq_sq₀ hρ0 ρ19_pos.le).mp hcb
  linarith

end CirclePacking
