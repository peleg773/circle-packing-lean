import CirclePacking.BnB

/-!
# From packings to canonical configurations

* `IsPacking c ρ`: centres in the closed disk of radius `ρ`, pairwise distance `≥ 2`.
* push-out: centres with `‖c‖² > ρ² - 4` are moved radially to the circle of radius `ρ`.
* canonicalisation: rotate the interior point of maximal radius to angle `0`, sort the other interior
  points by angle, reflect if necessary.
-/

open Real

namespace CirclePacking

/-- `n` unit circles in a circle of radius `ρ + 1`: centres in the closed disk of radius `ρ`,
pairwise distance at least `2`. -/
def IsPacking {n : ℕ} (c : Fin n → ℂ) (ρ : ℝ) : Prop :=
  (∀ i, ‖c i‖ ≤ ρ) ∧ ∀ i j, i ≠ j → 2 ≤ ‖c i - c j‖

/-- Admissible canonical configuration with a real container parameter `ρ` and real radius bounds. -/
structure AdmR (n k : ℕ) (ρ : ℝ) (L : ℕ → ℝ) (s ψ : ℕ → ℝ) (a : Fin (n - k) → ℝ) : Prop where
  s_nonneg : ∀ j < k, 0 ≤ s j
  s_sq : ∀ j < k, s j ^ 2 ≤ ρ ^ 2 - 4
  ii : ∀ i < k, ∀ j < k, i ≠ j →
    4 ≤ s i ^ 2 + s j ^ 2 - 2 * s i * s j * Real.cos (2 * π * (ψ i - ψ j))
  ib : ∀ b, ∀ j < k, 4 ≤ ρ ^ 2 + s j ^ 2 - 2 * ρ * s j * Real.cos (2 * π * (a b - ψ j))
  bb : ∀ b b', b ≠ b' → 4 ≤ 2 * ρ ^ 2 - 2 * ρ ^ 2 * Real.cos (2 * π * (a b - a b'))
  ψ01 : ∀ j < k, 0 ≤ ψ j ∧ ψ j ≤ 1
  smax : ∀ j < k, s j ≤ s 0
  ψ0 : 0 < k → ψ 0 = 0
  ord : ∀ j, 1 ≤ j → j + 1 < k → ψ j ≤ ψ (j + 1)
  refl : 3 ≤ k → ψ 1 + ψ (k - 1) ≤ 1
  rb : ∀ T : Finset ℕ, (∀ i ∈ T, i < k) → 0 < T.card → T.card < n → ∃ i ∈ T, L T.card ≤ s i

/-- monotonicity in the container parameter: from `ρ'` to `sc P.ρ ≥ ρ'` -/
theorem AdmR.toAdm {n k : ℕ} {ρ' : ℝ} {s ψ : ℕ → ℝ} {a : Fin (n - k) → ℝ} {P : Params}
    (hn : P.n = n) (hk : P.k = k) (h2 : 2 ≤ ρ') (hρ : ρ' ≤ sc P.ρ)
    (hA : AdmR n k ρ' (fun m => sc (P.L m)) s ψ a) :
    Adm P s ψ (fun b => a (Fin.cast (by rw [hn, hk]) b)) := by
  subst hn; subst hk
  have hρ0 : 0 < ρ' := by linarith
  refine ⟨hA.s_nonneg, ?_, hA.ii, ?_, ?_, hA.ψ01, hA.smax, hA.ψ0, hA.ord, hA.refl, hA.rb⟩
  · intro j hj
    have := hA.s_sq j hj
    nlinarith
  · intro b j hj
    have h := hA.ib (Fin.cast (by rfl) b) j hj
    have hs2 := hA.s_sq j hj
    have hs0 := hA.s_nonneg j hj
    set R := sc P.ρ
    set c := Real.cos (2 * π * (a (Fin.cast rfl b) - ψ j))
    have key : ρ' * (R ^ 2 + s j ^ 2 - 2 * R * s j * c - 4) - R * (ρ' ^ 2 + s j ^ 2 - 2 * ρ' * s j * c - 4)
        = (R - ρ') * (ρ' * R - s j ^ 2 + 4) := by ring
    have hpos : 0 ≤ (R - ρ') * (ρ' * R - s j ^ 2 + 4) := by
      apply mul_nonneg (by linarith); nlinarith
    have : 0 ≤ ρ' * (R ^ 2 + s j ^ 2 - 2 * R * s j * c - 4) := by nlinarith
    have h3 : 0 ≤ R ^ 2 + s j ^ 2 - 2 * R * s j * c - 4 := by
      by_contra hc; push Not at hc
      have := mul_neg_of_pos_of_neg hρ0 hc; linarith
    linarith
  · intro b b' hbb
    have h := hA.bb (Fin.cast rfl b) (Fin.cast rfl b') (by simpa using hbb)
    have hc := Real.cos_le_one (2 * π * (a (Fin.cast rfl b) - a (Fin.cast rfl b')))
    have : ρ' ^ 2 ≤ sc P.ρ ^ 2 := by nlinarith
    nlinarith

/-! ### Push-out -/

/-- push centres with `‖c‖² > ρ² - 4` radially onto the circle of radius `ρ` -/
noncomputable def pushOut (ρ : ℝ) {n : ℕ} (c : Fin n → ℂ) : Fin n → ℂ := fun i =>
  if ρ ^ 2 - 4 < ‖c i‖ ^ 2 then ((ρ / ‖c i‖ : ℝ) : ℂ) * c i else c i

lemma norm_pushed {ρ : ℝ} {z : ℂ} (hz : 0 < ‖z‖) (hρ : 0 ≤ ρ) : ‖((ρ / ‖z‖ : ℝ) : ℂ) * z‖ = ρ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  field_simp

theorem pushOut_spec {ρ : ℝ} (hρ : 2 < ρ) {n : ℕ} {c : Fin n → ℂ} (hc : IsPacking c ρ) :
    IsPacking (pushOut ρ c) ρ ∧
    (∀ i, ‖pushOut ρ c i‖ ^ 2 ≤ ρ ^ 2 - 4 ∨ ‖pushOut ρ c i‖ = ρ) ∧
    (∀ i, ‖pushOut ρ c i‖ ^ 2 ≤ ρ ^ 2 - 4 → pushOut ρ c i = c i) := by
  obtain ⟨hn, hd⟩ := hc
  have hpos : ∀ i, ρ ^ 2 - 4 < ‖c i‖ ^ 2 → 0 < ‖c i‖ := by
    intro i h
    rcases (norm_nonneg (c i)).lt_or_eq with h' | h'
    · exact h'
    · rw [← h'] at h; nlinarith
  have hnorm : ∀ i, ρ ^ 2 - 4 < ‖c i‖ ^ 2 → ‖pushOut ρ c i‖ = ρ := by
    intro i h
    simp only [pushOut, if_pos h]
    exact norm_pushed (hpos i h) (by linarith)
  have hfix : ∀ i, ¬ (ρ ^ 2 - 4 < ‖c i‖ ^ 2) → pushOut ρ c i = c i := by
    intro i h; simp only [pushOut, if_neg h]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro i
    by_cases h : ρ ^ 2 - 4 < ‖c i‖ ^ 2
    · rw [hnorm i h]
    · rw [hfix i h]; exact hn i
  · intro i j hij
    by_cases hi : ρ ^ 2 - 4 < ‖c i‖ ^ 2 <;> by_cases hj : ρ ^ 2 - 4 < ‖c j‖ ^ 2
    · -- both pushed
      have h1 : 2 ≤ ‖((ρ / ‖c i‖ : ℝ) : ℂ) * c i - c j‖ := pushout_pair hi (hn i) (hn j) (hd i j hij)
      have hnorm_i : ‖((ρ / ‖c i‖ : ℝ) : ℂ) * c i‖ ≤ ρ := by rw [norm_pushed (hpos i hi) (by linarith)]
      have h2 := pushout_pair hj (hn j) hnorm_i (by rw [norm_sub_rev]; exact h1)
      simp only [pushOut, if_pos hi, if_pos hj]
      rw [norm_sub_rev]; exact h2
    · have h1 : 2 ≤ ‖((ρ / ‖c i‖ : ℝ) : ℂ) * c i - c j‖ := pushout_pair hi (hn i) (hn j) (hd i j hij)
      simp only [pushOut, if_pos hi, if_neg hj]; exact h1
    · have h1 := pushout_pair hj (hn j) (hn i) (hd j i (Ne.symm hij))
      simp only [pushOut, if_neg hi, if_pos hj]
      rw [norm_sub_rev]; exact h1
    · simp only [pushOut, if_neg hi, if_neg hj]; exact hd i j hij
  · intro i
    by_cases h : ρ ^ 2 - 4 < ‖c i‖ ^ 2
    · right; exact hnorm i h
    · left; rw [hfix i h]; exact not_lt.mp h
  · intro i hi
    by_cases h : ρ ^ 2 - 4 < ‖c i‖ ^ 2
    · exfalso; rw [hnorm i h] at hi; linarith
    · exact hfix i h

/-! ### Angles and isometries -/

/-- the angle of `z` in turns, in `[0, 1)` -/
noncomputable def toTurn (z : ℂ) : ℝ := Int.fract (Complex.arg z / (2 * π))

lemma polar_toTurn (z : ℂ) : polar ‖z‖ (toTurn z) = z := by
  have h := polar_norm_arg z
  unfold toTurn
  have e : Int.fract (Complex.arg z / (2 * π)) =
      Complex.arg z / (2 * π) + ((-⌊Complex.arg z / (2 * π)⌋ : ℤ) : ℝ) := by
    rw [Int.fract]; push_cast; ring
  rw [e, polar_add_int]
  exact h

lemma toTurn_mem (z : ℂ) : 0 ≤ toTurn z ∧ toTurn z < 1 := ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

lemma toTurn_of_nonneg_real {x : ℝ} (hx : 0 ≤ x) : toTurn (x : ℂ) = 0 := by
  unfold toTurn; rw [Complex.arg_ofReal_of_nonneg hx]; simp

lemma polar_neg_angle (r t : ℝ) : polar r (-t) = (starRingEnd ℂ) (polar r t) := by
  apply Complex.ext <;> simp [polar, Real.cos_neg, Real.sin_neg]

lemma polar_one_sub (r t : ℝ) : polar r (1 - t) = (starRingEnd ℂ) (polar r t) := by
  rw [show (1 : ℝ) - t = -t + ((1 : ℤ) : ℝ) by push_cast; ring, polar_add_int, polar_neg_angle]

lemma dist_sq_of_polar {z w : ℂ} {r1 t1 r2 t2 : ℝ} (hz : z = polar r1 t1) (hw : w = polar r2 t2)
    (h : 2 ≤ ‖z - w‖) : 4 ≤ r1 ^ 2 + r2 ^ 2 - 2 * r1 * r2 * Real.cos (2 * π * (t1 - t2)) := by
  rw [← normSq_polar_sub, ← hz, ← hw]
  nlinarith [norm_nonneg (z - w)]

/-- multiplication by a unit complex number or composition with conjugation: an isometry fixing `0` -/
lemma isom_mul {u : ℂ} (hu : ‖u‖ = 1) (z w : ℂ) : ‖u * z - u * w‖ = ‖z - w‖ := by
  rw [← mul_sub, norm_mul, hu, one_mul]

lemma isom_conj (z w : ℂ) : ‖(starRingEnd ℂ) z - (starRingEnd ℂ) w‖ = ‖z - w‖ := by
  rw [← map_sub, Complex.norm_conj]

/-! ### Canonical form -/

/-- radius bounds valid for all packings with fewer than `n` points -/
def RadiusBounds (n : ℕ) (L : ℕ → ℝ) : Prop :=
  ∀ m, 0 < m → m < n → ∀ (d : Fin m → ℂ) (r : ℝ), IsPacking d r → L m ≤ r

/-- verification of `AdmR` from a labelled configuration in polar form -/
theorem admR_of_data {n k : ℕ} {ρ : ℝ} {L : ℕ → ℝ} (hL : RadiusBounds n L)
    (F : Fin n → ℂ) (hFd : ∀ i j, i ≠ j → 2 ≤ ‖F i - F j‖)
    (idx : ℕ → Fin n) (hidx : ∀ i j, i < k → j < k → idx i = idx j → i = j)
    (bdE : Fin (n - k) → Fin n) (hbd_inj : Function.Injective bdE)
    (hdisj : ∀ b j, j < k → bdE b ≠ idx j)
    (φ : Fin n → ℝ) (hpolar : ∀ i, F i = polar ‖F i‖ (φ i))
    (hint : ∀ j < k, ‖F (idx j)‖ ^ 2 ≤ ρ ^ 2 - 4) (hbdn : ∀ b, ‖F (bdE b)‖ = ρ)
    (h01 : ∀ j < k, 0 ≤ φ (idx j) ∧ φ (idx j) ≤ 1) (hmax : ∀ j < k, ‖F (idx j)‖ ≤ ‖F (idx 0)‖)
    (h0 : 0 < k → φ (idx 0) = 0) (hord : ∀ j, 1 ≤ j → j + 1 < k → φ (idx j) ≤ φ (idx (j + 1)))
    (hrefl : 3 ≤ k → φ (idx 1) + φ (idx (k - 1)) ≤ 1) :
    AdmR n k ρ L (fun j => ‖F (idx j)‖) (fun j => φ (idx j)) (fun b => φ (bdE b)) := by
  classical
  refine ⟨fun j _ => norm_nonneg _, hint, ?_, ?_, ?_, h01, hmax, h0, hord, hrefl, ?_⟩
  · intro i hi j hj hij
    have hne : idx i ≠ idx j := fun h => hij (hidx i j hi hj h)
    exact dist_sq_of_polar (hpolar _) (hpolar _) (hFd _ _ hne)
  · intro b j hj
    have h := dist_sq_of_polar (hpolar (bdE b)) (hpolar (idx j)) (hFd _ _ (hdisj b j hj))
    rw [hbdn b] at h
    exact h
  · intro b b' hbb
    have h := dist_sq_of_polar (hpolar (bdE b)) (hpolar (bdE b')) (hFd _ _ (hbd_inj.ne hbb))
    rw [hbdn b, hbdn b'] at h
    linarith
  · intro T hT hT0 hTn
    obtain ⟨i1, hi1T, hi1max⟩ := Finset.exists_max_image T (fun i => ‖F (idx i)‖)
      (Finset.card_pos.mp hT0)
    let e : Fin T.card ↪o ℕ := T.orderEmbOfFin rfl
    have he_mem : ∀ t, e t ∈ T := fun t => T.orderEmbOfFin_mem rfl t
    let g : Fin T.card → ℂ := fun t => F (idx (e t))
    have hg : IsPacking g ‖F (idx i1)‖ := by
      refine ⟨fun t => hi1max _ (he_mem t), ?_⟩
      intro t t' htt
      apply hFd
      intro h
      apply htt
      have := hidx _ _ (hT _ (he_mem t)) (hT _ (he_mem t')) h
      exact e.injective this
    exact ⟨i1, hi1T, hL T.card hT0 hTn g _ hg⟩

/-- every pushed-out configuration has a canonical form -/
theorem exists_canonical {n : ℕ} (hn0 : 0 < n) {ρ : ℝ} (hρ : 2 < ρ) {L : ℕ → ℝ} (hL : RadiusBounds n L)
    (d : Fin n → ℂ) (hd : IsPacking d ρ) (hIB : ∀ i, ‖d i‖ ^ 2 ≤ ρ ^ 2 - 4 ∨ ‖d i‖ = ρ) :
    ∃ k ≤ n, ∃ (s ψ : ℕ → ℝ) (a : Fin (n - k) → ℝ), AdmR n k ρ L s ψ a := by
  classical
  obtain ⟨hdn, hdd⟩ := hd
  set I : Finset (Fin n) := Finset.univ.filter (fun i => ‖d i‖ ^ 2 ≤ ρ ^ 2 - 4) with hIdef
  set k := I.card with hk
  have hmemI : ∀ i, i ∈ I ↔ ‖d i‖ ^ 2 ≤ ρ ^ 2 - 4 := fun i => by simp [hIdef]
  have hkn : k ≤ n := by
    calc k ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = n := by simp
  refine ⟨k, hkn, ?_⟩
  -- boundary enumeration
  set Bd : Finset (Fin n) := Iᶜ with hBd
  have hBdcard : Bd.card = n - k := by rw [hBd, Finset.card_compl, Fintype.card_fin]
  let bdE : Fin (n - k) → Fin n := fun b => (Bd.equivFin.symm (Fin.cast hBdcard.symm b)).val
  have bdE_mem : ∀ b, bdE b ∈ Bd := fun b => (Bd.equivFin.symm _).property
  have bdE_inj : Function.Injective bdE := by
    intro b b' h
    have := Subtype.ext h
    simpa using this
  have bdE_norm : ∀ b, ‖d (bdE b)‖ = ρ := by
    intro b
    have h1 := bdE_mem b
    rw [hBd, Finset.mem_compl, hmemI] at h1
    rcases hIB (bdE b) with h | h
    · exact absurd h h1
    · exact h
  -- the rotation
  -- (case k = 0 handled by the same construction with i0 arbitrary)
  by_cases hk0 : k = 0
  · -- no interior points
    have hFd : ∀ i j, i ≠ j → 2 ≤ ‖d i - d j‖ := hdd
    have := admR_of_data hL d hFd (fun _ => (⟨0, hn0⟩ : Fin n)) (by intro i j hi; omega)
      bdE bdE_inj (by intro b j hj; omega) (fun i => toTurn (d i)) (fun i => (polar_toTurn (d i)).symm)
      (by intro j hj; omega) (fun b => bdE_norm b) (by intro j hj; omega) (by intro j hj; omega)
      (by intro h; omega) (by intro j _ hj; omega) (by intro h; omega)
    exact ⟨_, _, _, this⟩
  -- k ≥ 1: the interior point of maximal radius
  have hIne : I.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i0, hi0I, hi0max⟩ := Finset.exists_max_image I (fun i => ‖d i‖) hIne
  -- rotation `u` putting `d i0` on the non-negative real axis
  let u : ℂ := if d i0 = 0 then 1 else (starRingEnd ℂ) (d i0) / (‖d i0‖ : ℂ)
  have hu : ‖u‖ = 1 := by
    by_cases h : d i0 = 0
    · simp [u, h]
    · have hn : (0 : ℝ) < ‖d i0‖ := norm_pos_iff.mpr h
      simp only [u, h, if_false, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hn]
      field_simp
  have hui0 : u * d i0 = ((‖d i0‖ : ℝ) : ℂ) := by
    by_cases h : d i0 = 0
    · simp [u, h]
    · have hn : (0 : ℝ) < ‖d i0‖ := norm_pos_iff.mpr h
      have hcz : (starRingEnd ℂ) (d i0) * d i0 = ((‖d i0‖ ^ 2 : ℝ) : ℂ) := by
        rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      have hne : ((‖d i0‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      simp only [u, h, if_false]
      rw [div_mul_eq_mul_div, hcz, div_eq_iff hne]
      push_cast; ring
  let e : Fin n → ℂ := fun i => u * d i
  have he_norm : ∀ i, ‖e i‖ = ‖d i‖ := fun i => by simp [e, norm_mul, hu]
  have he_dist : ∀ i j, ‖e i - e j‖ = ‖d i - d j‖ := fun i j => isom_mul hu _ _
  let θ : Fin n → ℝ := fun i => toTurn (e i)
  have hθ0 : θ i0 = 0 := by
    simp only [θ, e]; rw [hui0]; exact toTurn_of_nonneg_real (norm_nonneg _)
  have hθmem : ∀ i, 0 ≤ θ i ∧ θ i < 1 := fun i => toTurn_mem _
  have he_polar : ∀ i, e i = polar ‖e i‖ (θ i) := fun i => (polar_toTurn (e i)).symm
  -- the other interior points, sorted by angle
  set J := I.erase i0 with hJ
  have hJcard : J.card = k - 1 := by rw [hJ, Finset.card_erase_of_mem hi0I]
  let enum : Fin (k - 1) → Fin n := fun j => (J.equivFin.symm (Fin.cast hJcard.symm j)).val
  have enum_mem : ∀ j, enum j ∈ J := fun j => (J.equivFin.symm _).property
  have enum_inj : Function.Injective enum := by
    intro j j' h
    have := Subtype.ext h
    simpa using this
  let σ := Tuple.sort (fun j => θ (enum j))
  let f : Fin (k - 1) → Fin n := fun j => enum (σ j)
  have hfmono : Monotone (fun j => θ (f j)) := Tuple.monotone_sort (fun j => θ (enum j))
  have hfJ : ∀ j, f j ∈ J := fun j => enum_mem _
  have hfinj : Function.Injective f := fun j j' h => σ.injective (enum_inj h)
  have hfI : ∀ j, f j ∈ I := fun j => Finset.mem_of_mem_erase (hfJ j)
  have hfne : ∀ j, f j ≠ i0 := fun j => Finset.ne_of_mem_erase (hfJ j)
  have hk1 : 1 ≤ k := by omega
  -- common facts
  have hbd_notI : ∀ b, bdE b ∉ I := fun b => by
    have := bdE_mem b; rwa [hBd, Finset.mem_compl] at this
  by_cases hrefl : ∃ h3 : 3 ≤ k, 1 < θ (f ⟨0, by omega⟩) + θ (f ⟨k - 2, by omega⟩)
  · -- reflected construction
    let F : Fin n → ℂ := fun i => (starRingEnd ℂ) (e i)
    let φ : Fin n → ℝ := fun i => if i = i0 then 0 else 1 - θ i
    let idx : ℕ → Fin n := fun j => if h : 1 ≤ j ∧ j - 1 < k - 1 then f ⟨k - 2 - (j - 1), by omega⟩ else i0
    have hF_norm : ∀ i, ‖F i‖ = ‖d i‖ := fun i => by simp [F, Complex.norm_conj, he_norm]
    have hFd : ∀ i j, i ≠ j → 2 ≤ ‖F i - F j‖ := fun i j h => by
      simp only [F]; rw [isom_conj, he_dist]; exact hdd i j h
    have hpolar : ∀ i, F i = polar ‖F i‖ (φ i) := by
      intro i
      rw [hF_norm]
      by_cases hi : i = i0
      · subst hi
        simp only [F, φ, if_true, e]
        rw [hui0, Complex.conj_ofReal]
        apply Complex.ext <;> simp [polar]
      · simp only [F, φ, hi, if_false]
        rw [polar_one_sub, ← he_norm, ← he_polar]
    have hidx0 : idx 0 = i0 := by simp [idx]
    have hidxS : ∀ j (hj : j < k - 1), idx (j + 1) = f ⟨k - 2 - j, by omega⟩ := by
      intro j hj
      simp only [idx]
      rw [dif_pos ⟨by omega, by omega⟩]
      congr 2
    have hidxI : ∀ j < k, idx j ∈ I := by
      intro j hj
      rcases Nat.eq_zero_or_pos j with rfl | hjp
      · rw [hidx0]; exact hi0I
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        rw [hidxS j' (by omega)]; exact hfI _
    have hidx_inj : ∀ i j, i < k → j < k → idx i = idx j → i = j := by
      intro i j hi hj h
      rcases Nat.eq_zero_or_pos i with rfl | hip <;> rcases Nat.eq_zero_or_pos j with rfl | hjp
      · rfl
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        rw [hidx0, hidxS j' (by omega)] at h
        exact absurd h.symm (hfne _)
      · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        rw [hidx0, hidxS i' (by omega)] at h
        exact absurd h (hfne _)
      · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        rw [hidxS i' (by omega), hidxS j' (by omega)] at h
        have := hfinj h
        simp only [Fin.mk.injEq] at this
        omega
    have hφidx : ∀ j (hj : j < k - 1), φ (idx (j + 1)) = 1 - θ (f ⟨k - 2 - j, by omega⟩) := by
      intro j hj
      rw [hidxS j hj]
      simp only [φ, hfne, if_false]
    have := admR_of_data hL F hFd idx hidx_inj bdE bdE_inj
      (fun b j hj h => hbd_notI b (h ▸ hidxI j hj)) φ hpolar
      (fun j hj => by rw [hF_norm]; exact (hmemI _).mp (hidxI j hj))
      (fun b => by rw [hF_norm]; exact bdE_norm b)
      (by
        intro j hj
        rcases Nat.eq_zero_or_pos j with rfl | hjp
        · rw [hidx0]; simp [φ]
        · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
          rw [hφidx j' (by omega)]
          have := hθmem (f ⟨k - 2 - j', by omega⟩)
          constructor <;> linarith)
      (by
        intro j hj
        rw [hF_norm, hF_norm, hidx0]
        exact hi0max _ (hidxI j hj))
      (fun _ => by rw [hidx0]; simp [φ])
      (by
        intro j hj1 hjk
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        rw [hφidx j' (by omega), hφidx (j' + 1) (by omega)]
        have := hfmono (show (⟨k - 2 - (j' + 1), by omega⟩ : Fin (k - 1)) ≤ ⟨k - 2 - j', by omega⟩ by
          simp only [Fin.mk_le_mk]; omega)
        simp only at this
        linarith)
      (by
        intro hk3
        obtain ⟨h3, hgt⟩ := hrefl
        have hl : idx (k - 1) = idx ((k - 2) + 1) := by congr 1; omega
        rw [hφidx 0 (by omega), hl, hφidx (k - 2) (by omega)]
        have e1 : (⟨k - 2 - 0, by omega⟩ : Fin (k - 1)) = ⟨k - 2, by omega⟩ := by simp
        have e2 : (⟨k - 2 - (k - 2), by omega⟩ : Fin (k - 1)) = ⟨0, by omega⟩ := by simp
        rw [e1, e2]
        linarith)
    exact ⟨_, _, _, this⟩
  · -- direct construction
    let idx : ℕ → Fin n := fun j => if h : 1 ≤ j ∧ j - 1 < k - 1 then f ⟨j - 1, h.2⟩ else i0
    have hidx0 : idx 0 = i0 := by simp [idx]
    have hidxS : ∀ j (hj : j < k - 1), idx (j + 1) = f ⟨j, hj⟩ := by
      intro j hj
      simp only [idx]
      rw [dif_pos ⟨by omega, by omega⟩]
      congr 2
    have hidxI : ∀ j < k, idx j ∈ I := by
      intro j hj
      rcases Nat.eq_zero_or_pos j with rfl | hjp
      · rw [hidx0]; exact hi0I
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        rw [hidxS j' (by omega)]; exact hfI _
    have hidx_inj : ∀ i j, i < k → j < k → idx i = idx j → i = j := by
      intro i j hi hj h
      rcases Nat.eq_zero_or_pos i with rfl | hip <;> rcases Nat.eq_zero_or_pos j with rfl | hjp
      · rfl
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        rw [hidx0, hidxS j' (by omega)] at h
        exact absurd h.symm (hfne _)
      · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        rw [hidx0, hidxS i' (by omega)] at h
        exact absurd h (hfne _)
      · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        rw [hidxS i' (by omega), hidxS j' (by omega)] at h
        have := hfinj h
        simp only [Fin.mk.injEq] at this
        omega
    have hFd : ∀ i j, i ≠ j → 2 ≤ ‖e i - e j‖ := fun i j h => by rw [he_dist]; exact hdd i j h
    have := admR_of_data hL e hFd idx hidx_inj bdE bdE_inj
      (fun b j hj h => hbd_notI b (h ▸ hidxI j hj)) θ he_polar
      (fun j hj => by rw [he_norm]; exact (hmemI _).mp (hidxI j hj))
      (fun b => by rw [he_norm]; exact bdE_norm b)
      (fun j hj => ⟨(hθmem _).1, (hθmem _).2.le⟩)
      (by
        intro j hj
        rw [he_norm, he_norm, hidx0]
        exact hi0max _ (hidxI j hj))
      (fun _ => by rw [hidx0]; exact hθ0)
      (by
        intro j hj1 hjk
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        rw [hidxS j' (by omega), hidxS (j' + 1) (by omega)]
        exact hfmono (show (⟨j', by omega⟩ : Fin (k - 1)) ≤ ⟨j' + 1, by omega⟩ by
          simp only [Fin.mk_le_mk]; omega))
      (by
        intro hk3
        have hl : idx (k - 1) = idx ((k - 2) + 1) := by congr 1; omega
        rw [hidxS 0 (by omega), hl, hidxS (k - 2) (by omega)]
        by_contra hc
        push Not at hc
        exact hrefl ⟨hk3, hc⟩)
    exact ⟨_, _, _, this⟩

end CirclePacking
