import CirclePacking.KFive16
import CirclePacking.Radius16
import CirclePacking.Main

/-!
# Optimal packing of 16 unit circles in a circle: assembly

`n16_lower`: every packing of 16 unit circles has container parameter `≥ ρ16` (given the branch-and-bound
certificates).  `cstar16_packing`: the record configuration `c*` is a packing with parameter `ρ16`.
-/

open Real Finset

namespace CirclePacking

/-- **Lower bound.** -/
theorem n16_lower
    (hrb : ∀ m, 8 ≤ m → m ≤ 11 → ∀ k ≤ m, Certified (Prb m k) (fun _ => false))
    (h12 : ∀ k ≤ 12, Certified (Prb12 k) (fun _ => false))
    (hchk : ∀ k ≤ 16, k ≠ 5 → Certified (P16 k) (fun _ => false))
    (hchk5 : Certified (P16 5) (survOK16 (P16 5)))
    (c : Fin 16 → ℂ) (r : ℝ) (hc : IsPacking c r) : ρ16 ≤ r := by
  have hRB := radiusBounds16 hrb h12
  by_contra hlt
  push Not at hlt
  have heps : (0 : ℝ) < ((epsR : ℚ) : ℝ) := by rw [epsR_real]; norm_num
  set ρ'' := max r (ρ16 - ((epsR : ℚ) : ℝ)) with hρdef
  have h1 : ρ16 - ((epsR : ℚ) : ℝ) ≤ ρ'' := le_max_right _ _
  have h2 : ρ'' < ρ16 := max_lt hlt (by linarith)
  have h3 : 2 < ρ'' := lt_of_lt_of_le (by linarith [two_lt_ρ16]) h1
  have hcp := hc.mono (le_max_left r (ρ16 - ((epsR : ℚ) : ℝ)))
  obtain ⟨hpk, hIB, -⟩ := pushOut_spec h3 hcp
  obtain ⟨k, hk, s, ψ, a, hA⟩ := exists_canonical (by norm_num) h3 hRB _ hpk hIB
  have hρP : ρ'' ≤ sc (P16 k).ρ := le_trans h2.le (ρ16_le_P16 k)
  by_cases hk5 : k = 5
  · subst hk5
    have hAd := AdmR.toAdm (P := P16 5) rfl rfl h3.le hρP hA
    obtain ⟨b, hb, hF⟩ := hchk5.2 _ _ _ hAd
    exact k5_impossible16 h1 h2 h3.le hρP hA hb hF
  · have hAd := AdmR.toAdm (P := P16 k) rfl rfl h3.le hρP hA
    obtain ⟨b, hb, -⟩ := (hchk k hk hk5).2 _ _ _ hAd
    exact absurd hb (by simp)

/-! ### `c*` is a packing -/

/-- squared distance of points `i`, `j` of `c̃`, minus a margin covering `|c* - c̃| ≤ rb` -/
def dist16LB (i j : ℕ) : ℚ :=
  let dx := n16K.utq (2 * i) - n16K.utq (2 * j)
  let dy := n16K.utq (2 * i + 1) - n16K.utq (2 * j + 1)
  dx ^ 2 + dy ^ 2 - 4 * (|dx| + |dy|) * n16K.rb

def pack16OK : Bool :=
  (List.range 16).all (fun i => (List.range 16).all (fun j =>
    decide (j ≤ i) || decide ((i, j) ∈ n16ctc) || decide (4 ≤ dist16LB i j))) &&
  (List.range 5).all (fun p => decide (((r16Hi.getD p 0 : ℚ) / S) ^ 2 ≤ P16lo))

set_option maxRecDepth 100000 in
theorem pack16OK_true : pack16OK = true := by decide +kernel

lemma dist_C16_sq (i j : ℕ) : ‖C16 i - C16 j‖ ^ 2 =
    (u16 (2 * i) - u16 (2 * j)) ^ 2 + (u16 (2 * i + 1) - u16 (2 * j + 1)) ^ 2 := by
  rw [sq_norm_eq]; simp [C16]

lemma C16_dist_ge {i j : ℕ} (hi : i < 16) (hj : j < 16) (hij : i < j) : 4 ≤ ‖C16 i - C16 j‖ ^ 2 := by
  have h := pack16OK_true
  unfold pack16OK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h.1 i hi j hj with (hle | hmem) | hd
  · omega
  · -- a contact pair
    obtain ⟨r, hr, hrr⟩ := List.mem_iff_getElem.mp hmem
    have hr21 : r < 21 := hr
    have hci : n16K.ci r = i := by
      unfold KData.ci; simp [n16K, List.getD_eq_getElem?_getD, hr, hrr]
    have hcj : n16K.cj r = j := by
      unfold KData.cj; simp [n16K, List.getD_eq_getElem?_getD, hr, hrr]
    have := C16_contact hr21
    rw [hci, hcj] at this
    rw [dist_C16_sq, this]
  · rw [dist_C16_sq]
    have hd' := (Rat.cast_le (K := ℝ)).mpr hd
    simp only [dist16LB] at hd'
    push_cast at hd'
    have a1 := u16_near (k := 2 * i) (by omega)
    have a2 := u16_near (k := 2 * j) (by omega)
    have a3 := u16_near (k := 2 * i + 1) (by omega)
    have a4 := u16_near (k := 2 * j + 1) (by omega)
    have bx : |(u16 (2 * i) - u16 (2 * j)) - ((n16K.utq (2 * i) : ℝ) - n16K.utq (2 * j))| ≤ 2 * n16K.rb := by
      calc _ = |(u16 (2 * i) - n16K.utq (2 * i)) - (u16 (2 * j) - n16K.utq (2 * j))| := by ring_nf
        _ ≤ _ := abs_sub _ _
        _ ≤ _ := by linarith
    have bY : |(u16 (2 * i + 1) - u16 (2 * j + 1)) - ((n16K.utq (2 * i + 1) : ℝ) - n16K.utq (2 * j + 1))| ≤
        2 * n16K.rb := by
      calc _ = |(u16 (2 * i + 1) - n16K.utq (2 * i + 1)) - (u16 (2 * j + 1) - n16K.utq (2 * j + 1))| := by ring_nf
        _ ≤ _ := abs_sub _ _
        _ ≤ _ := by linarith
    have l1 := sq_lower bx
    have l2 := sq_lower bY
    nlinarith

theorem cstar16_packing : IsPacking (fun i : Fin 16 => C16 i) ρ16 := by
  have h := pack16OK_true
  unfold pack16OK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · by_cases hi5 : (i : ℕ) < 5
    · have hr := (C16_radius (p := i) (by omega)).2
      have hsq := h.2 i hi5
      have hsq' := (Rat.cast_le (K := ℝ)).mpr hsq
      push_cast at hsq'
      have hb := P16s_bounds.1
      have hS := S_pos
      have h0 : 0 ≤ ‖C16 i‖ := norm_nonneg _
      have : ‖C16 i‖ ^ 2 ≤ ρ16 ^ 2 := by
        rw [ρ16_sq]
        have : ‖C16 i‖ ^ 2 ≤ sc (r16Hi.getD i 0) ^ 2 := pow_le_pow_left₀ h0 hr 2
        unfold sc at this
        have e : ((r16Hi.getD (↑i) 0 : ℝ) / S) ^ 2 = ((r16Hi.getD (↑i) 0 : ℚ) : ℝ) ^ 2 / (S : ℝ) ^ 2 := by
          push_cast; ring
        rw [e] at this
        have e2 : ((r16Hi.getD (↑i) 0 : ℚ) : ℝ) ^ 2 / (S : ℝ) ^ 2 = (((r16Hi.getD (↑i) 0 : ℚ) : ℝ) / S) ^ 2 := by
          ring
        linarith
      exact le_of_pow_le_pow_left₀ two_ne_zero ρ16_pos.le this
    · have : (i : ℕ) = 5 + ((i : ℕ) - 5) := by omega
      have hb := C16_bnd_norm (t := (i : ℕ) - 5) (by omega)
      rw [← this] at hb
      simp only
      rw [hb]
  · have hne : (i : ℕ) ≠ j := fun h' => hij (Fin.ext h')
    have hsq : 4 ≤ ‖C16 i - C16 j‖ ^ 2 := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact C16_dist_ge i.isLt j.isLt hlt
      · rw [norm_sub_rev]; exact C16_dist_ge j.isLt i.isLt hgt
    nlinarith [norm_nonneg (C16 i - C16 j)]

end CirclePacking
