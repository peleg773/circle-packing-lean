import CirclePacking.CosTurn
import CirclePacking.Greedy
import CirclePacking.Polar

/-!
# Boxes of interior points and the elementary pruning tests (integer version)

An interior point is described by its radius `s` and angle `ψ` (in turns).  A box for one interior
point is an `IBox` (defined in `C15Compute`) of integer bounds in units of `1/S`.
-/

open Real

namespace CirclePacking

/-- `(s, ψ)` lies in the box `I`. -/
def InI (I : IBox) (s ψ : ℝ) : Prop := sc I.slo ≤ s ∧ s ≤ sc I.shi ∧ sc I.plo ≤ ψ ∧ ψ ≤ sc I.phi

lemma sc_mul_S (x : ℤ) : sc x * S = x := by unfold sc; field_simp [S_pos.ne']

lemma sc_zero : sc 0 = 0 := by simp [sc]

lemma sc_nonneg {x : ℤ} (h : 0 ≤ x) : 0 ≤ sc x := by
  have := sc_le_iff.mpr h; rwa [sc_zero] at this

lemma sc_pos {x : ℤ} (h : 0 < x) : 0 < sc x := by
  have := sc_lt_iff.mpr h; rwa [sc_zero] at this

/-! ### Corner lemmas -/

lemma quad_le_max {β γ l h x : ℝ} (hl : l ≤ x) (hh : x ≤ h) :
    x ^ 2 + β * x + γ ≤ max (l ^ 2 + β * l + γ) (h ^ 2 + β * h + γ) := by
  by_cases hc : x + l + β ≤ 0
  · have : x ^ 2 + β * x + γ ≤ l ^ 2 + β * l + γ := by nlinarith
    exact le_trans this (le_max_left _ _)
  · push Not at hc
    have : x ^ 2 + β * x + γ ≤ h ^ 2 + β * h + γ := by nlinarith
    exact le_trans this (le_max_right _ _)

/-- `x² + y² - 2 c x y` on a rectangle is bounded by its corner values -/
lemma Q_le_corners {c l1 h1 l2 h2 x y : ℝ} (hx1 : l1 ≤ x) (hx2 : x ≤ h1) (hy1 : l2 ≤ y) (hy2 : y ≤ h2)
    {B : ℝ} (hc1 : l1 ^ 2 + l2 ^ 2 - 2 * c * l1 * l2 ≤ B) (hc2 : l1 ^ 2 + h2 ^ 2 - 2 * c * l1 * h2 ≤ B)
    (hc3 : h1 ^ 2 + l2 ^ 2 - 2 * c * h1 * l2 ≤ B) (hc4 : h1 ^ 2 + h2 ^ 2 - 2 * c * h1 * h2 ≤ B) :
    x ^ 2 + y ^ 2 - 2 * c * x * y ≤ B := by
  have hq1 := quad_le_max (β := -2 * c * y) (γ := y ^ 2) hx1 hx2
  have hq2 := quad_le_max (β := -2 * c * l1) (γ := l1 ^ 2) hy1 hy2
  have hq3 := quad_le_max (β := -2 * c * h1) (γ := h1 ^ 2) hy1 hy2
  have e : x ^ 2 + y ^ 2 - 2 * c * x * y = x ^ 2 + (-2 * c * y) * x + y ^ 2 := by ring
  rw [e]
  refine le_trans hq1 (max_le ?_ ?_)
  · have e2 : l1 ^ 2 + (-2 * c * y) * l1 + y ^ 2 = y ^ 2 + (-2 * c * l1) * y + l1 ^ 2 := by ring
    rw [e2]
    refine le_trans hq2 (max_le ?_ ?_) <;> nlinarith
  · have e2 : h1 ^ 2 + (-2 * c * y) * h1 + y ^ 2 = y ^ 2 + (-2 * c * h1) * y + h1 ^ 2 := by ring
    rw [e2]
    refine le_trans hq3 (max_le ?_ ?_) <;> nlinarith

/-- `φ(s) = (s² + c)/(2 t s)` on `[l, h]` (`l > 0`, `t > 0`) is bounded by its endpoint values. -/
lemma phi_le_max {c t l h s : ℝ} (ht : 0 < t) (hl0 : 0 < l) (hl : l ≤ s) (hh : s ≤ h) :
    (s ^ 2 + c) / (2 * t * s) ≤ max ((l ^ 2 + c) / (2 * t * l)) ((h ^ 2 + c) / (2 * t * h)) := by
  have hs0 : 0 < s := lt_of_lt_of_le hl0 hl
  have hh0 : 0 < h := lt_of_lt_of_le hs0 hh
  by_cases hc : s * l ≤ c
  · apply le_trans _ (le_max_left _ _)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hc), ht]
  · push Not at hc
    apply le_trans _ (le_max_right _ _)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : c < s * h := lt_of_lt_of_le hc (by nlinarith)
    nlinarith [mul_nonneg (sub_nonneg.mpr hh) (sub_nonneg.mpr this.le), ht]

lemma f_le_max_x {l h x y : ℝ} (hl0 : 0 < l) (hl : l ≤ x) (hh : x ≤ h) (hy : 0 < y) :
    (x ^ 2 + y ^ 2 - 4) / (2 * x * y) ≤
      max ((l ^ 2 + y ^ 2 - 4) / (2 * l * y)) ((h ^ 2 + y ^ 2 - 4) / (2 * h * y)) := by
  have h1 := phi_le_max (c := y ^ 2 - 4) (t := y) hy hl0 hl hh
  have e : ∀ u : ℝ, (u ^ 2 + y ^ 2 - 4) / (2 * u * y) = (u ^ 2 + (y ^ 2 - 4)) / (2 * y * u) := by
    intro u; ring_nf
  rw [e x, e l, e h]
  exact h1

lemma f_symm (x y : ℝ) : (x ^ 2 + y ^ 2 - 4) / (2 * x * y) = (y ^ 2 + x ^ 2 - 4) / (2 * y * x) := by
  ring_nf

/-- `(x² + y² - 4)/(2xy)` on a positive rectangle is bounded by its corner values -/
lemma f_le_corners {l1 h1 l2 h2 x y : ℝ} (hl1 : 0 < l1) (hl2 : 0 < l2) (hx1 : l1 ≤ x) (hx2 : x ≤ h1)
    (hy1 : l2 ≤ y) (hy2 : y ≤ h2) {B : ℝ}
    (hc1 : (l1 ^ 2 + l2 ^ 2 - 4) / (2 * l1 * l2) ≤ B) (hc2 : (l1 ^ 2 + h2 ^ 2 - 4) / (2 * l1 * h2) ≤ B)
    (hc3 : (h1 ^ 2 + l2 ^ 2 - 4) / (2 * h1 * l2) ≤ B) (hc4 : (h1 ^ 2 + h2 ^ 2 - 4) / (2 * h1 * h2) ≤ B) :
    (x ^ 2 + y ^ 2 - 4) / (2 * x * y) ≤ B := by
  have hx0 : 0 < x := lt_of_lt_of_le hl1 hx1
  have hy0 : 0 < y := lt_of_lt_of_le hl2 hy1
  have hh1 : 0 < h1 := lt_of_lt_of_le hx0 hx2
  refine le_trans (f_le_max_x hl1 hx1 hx2 hy0) (max_le ?_ ?_)
  · rw [f_symm]
    refine le_trans (f_le_max_x hl2 hy1 hy2 hl1) (max_le ?_ ?_)
    · rw [f_symm]; exact hc1
    · rw [f_symm]; exact hc2
  · rw [f_symm]
    refine le_trans (f_le_max_x hl2 hy1 hy2 hh1) (max_le ?_ ?_)
    · rw [f_symm]; exact hc3
    · rw [f_symm]; exact hc4

/-! ### The integer corner tests -/

lemma S3_pos : (0 : ℝ) < (S : ℝ) * S * S := by have := S_pos; positivity

lemma quadLt4_sound {c x y : ℤ} (h : quadLt4 c x y = true) :
    sc x ^ 2 + sc y ^ 2 - 2 * sc c * sc x * sc y < 4 := by
  unfold quadLt4 at h
  simp only [decide_eq_true_eq] at h
  have h' : ((x * x * S + y * y * S - 2 * c * x * y : ℤ) : ℝ) < ((4 * S * S * S : ℤ) : ℝ) := by
    exact_mod_cast h
  push_cast at h'
  have hS := S_pos
  unfold sc
  rw [← sub_neg]
  have e : (x : ℝ) / S ^ 1 = (x : ℝ) / S := by ring
  have key : ((x : ℝ) / S) ^ 2 + ((y : ℝ) / S) ^ 2 - 2 * ((c : ℝ) / S) * ((x : ℝ) / S) * ((y : ℝ) / S) - 4
      = ((x : ℝ) * x * S + y * y * S - 2 * c * x * y - 4 * S * S * S) / (S * S * S) := by
    field_simp
  rw [key]
  apply div_neg_of_neg_of_pos (by linarith) S3_pos

lemma corners_quad {c : ℤ} {I J : IBox} (h : corners (quadLt4 c) I J = true) {x y : ℝ}
    (hx1 : sc I.slo ≤ x) (hx2 : x ≤ sc I.shi) (hy1 : sc J.slo ≤ y) (hy2 : y ≤ sc J.shi) :
    x ^ 2 + y ^ 2 - 2 * sc c * x * y < 4 := by
  unfold corners at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have := Q_le_corners (c := sc c) (B := max (max (sc I.slo ^ 2 + sc J.slo ^ 2 - 2 * sc c * sc I.slo * sc J.slo)
      (sc I.slo ^ 2 + sc J.shi ^ 2 - 2 * sc c * sc I.slo * sc J.shi))
      (max (sc I.shi ^ 2 + sc J.slo ^ 2 - 2 * sc c * sc I.shi * sc J.slo)
      (sc I.shi ^ 2 + sc J.shi ^ 2 - 2 * sc c * sc I.shi * sc J.shi))) hx1 hx2 hy1 hy2
    (le_trans (le_max_left _ _) (le_max_left _ _)) (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_trans (le_max_left _ _) (le_max_right _ _)) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hb := max_lt (max_lt (quadLt4_sound h1) (quadLt4_sound h2)) (max_lt (quadLt4_sound h3) (quadLt4_sound h4))
  linarith

lemma fLe_sound {c x y : ℤ} (hx : 0 < x) (hy : 0 < y) (h : fLe c x y = true) :
    (sc x ^ 2 + sc y ^ 2 - 4) / (2 * sc x * sc y) ≤ sc c := by
  unfold fLe at h
  simp only [decide_eq_true_eq] at h
  have h' : (((x * x + y * y - 4 * S * S) * S : ℤ) : ℝ) ≤ ((c * (2 * x * y) : ℤ) : ℝ) := by
    exact_mod_cast h
  push_cast at h'
  have hS := S_pos
  have hx' : (0 : ℝ) < x := by exact_mod_cast hx
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  unfold sc
  rw [div_le_iff₀ (by positivity)]
  have key : (((x : ℝ) / S) ^ 2 + ((y : ℝ) / S) ^ 2 - 4) = ((x : ℝ) * x + y * y - 4 * S * S) / (S * S) := by
    field_simp
  have key2 : (c : ℝ) / S * (2 * ((x : ℝ) / S) * ((y : ℝ) / S)) = (c * (2 * x * y)) / (S * S * S) := by
    field_simp
  rw [key, key2, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

lemma corners_f {c : ℤ} {I J : IBox} (hI : 0 < I.slo) (hJ : 0 < J.slo) (h : corners (fLe c) I J = true)
    {x y : ℝ} (hx1 : sc I.slo ≤ x) (hx2 : x ≤ sc I.shi) (hy1 : sc J.slo ≤ y) (hy2 : y ≤ sc J.shi) :
    (x ^ 2 + y ^ 2 - 4) / (2 * x * y) ≤ sc c := by
  unfold corners at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hIh : 0 < I.shi := by
    have h0 : sc 0 < sc I.shi := by rw [sc_zero]; exact lt_of_lt_of_le (sc_pos hI) (le_trans hx1 hx2)
    exact sc_lt_iff.mp h0
  have hJh : 0 < J.shi := by
    have h0 : sc 0 < sc J.shi := by rw [sc_zero]; exact lt_of_lt_of_le (sc_pos hJ) (le_trans hy1 hy2)
    exact sc_lt_iff.mp h0
  exact f_le_corners (sc_pos hI) (sc_pos hJ) hx1 hx2 hy1 hy2 (fLe_sound hI hJ h1) (fLe_sound hI hJh h2)
    (fLe_sound hIh hJ h3) (fLe_sound hIh hJh h4)

/-! ### Circular distance -/

lemma cos_turn_le {x t : ℝ} {m : ℤ} (ht : t ≤ 1 / 2) (h : |x - m| ≤ t) :
    Real.cos (2 * π * t) ≤ Real.cos (2 * π * x) := by
  have e1 : Real.cos (2 * π * x) = Real.cos (2 * π * |x - m|) := by
    have h2 : 2 * π * |x - m| = |2 * π * (x - m)| := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
    rw [h2, Real.cos_abs]
    have : 2 * π * (x - m) = 2 * π * x + (-m : ℤ) * (2 * π) := by push_cast; ring
    rw [this, Real.cos_add_int_mul_two_pi]
  rw [e1]
  apply Real.cos_le_cos_of_nonneg_of_le_pi
  · positivity
  · nlinarith [Real.pi_pos]
  · nlinarith [Real.pi_pos]

/-- the certified cosine bound in real form -/
lemma cosZ_sc {D : ℤ} (h0 : 0 ≤ D) (h1 : 2 * D ≤ S) : sc (cosZ D) ≤ Real.cos (2 * π * sc D) :=
  cosZ_le D h0 h1

lemma half_of_two_le {D : ℤ} (h : 2 * D ≤ S) : sc D ≤ 1 / 2 := by
  have := sc_le_iff.mpr h
  rw [show (2 : ℤ) * D = D + D by ring, sc_add, sc_S] at this
  linarith

lemma circBound_spec {I J : IBox} {D m : ℤ} (h : circBound I J = some (D, m)) {ψi ψj : ℝ}
    (hi1 : sc I.plo ≤ ψi) (hi2 : ψi ≤ sc I.phi) (hj1 : sc J.plo ≤ ψj) (hj2 : ψj ≤ sc J.phi)
    (hi01 : 0 ≤ ψi ∧ ψi ≤ 1) (hj01 : 0 ≤ ψj ∧ ψj ≤ 1) :
    |ψi - ψj - m| ≤ sc D ∧ 0 ≤ D ∧ 2 * D ≤ S := by
  have hS1 := sc_S
  have hnn : ∀ {D' : ℤ}, (∃ z : ℝ, |z| ≤ sc D') → 0 ≤ D' := by
    intro D' ⟨z, hz⟩
    have : sc 0 ≤ sc D' := by rw [sc_zero]; exact le_trans (abs_nonneg z) hz
    exact sc_le_iff.mp this
  unfold circBound at h
  split_ifs at h with c1 c2 c3
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have s1 := sc_le_iff.mpr (le_max_left (J.phi - I.plo) (I.phi - J.plo))
    have s2 := sc_le_iff.mpr (le_max_right (J.phi - I.plo) (I.phi - J.plo))
    rw [sc_sub] at s1 s2
    have habs : |ψi - ψj - ((0 : ℤ) : ℝ)| ≤ sc (max (J.phi - I.plo) (I.phi - J.plo)) := by
      push_cast; rw [abs_le]; constructor <;> linarith
    refine ⟨habs, hnn ⟨_, habs⟩, ?_⟩
    rcases le_total (J.phi - I.plo) (I.phi - J.plo) with hle | hle
    · rw [max_eq_right hle]; omega
    · rw [max_eq_left hle]; omega
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hlow : sc (I.plo - J.phi) ≤ ψi - ψj := by rw [sc_sub]; linarith
    have hD : sc (S - (I.plo - J.phi)) = 1 - sc (I.plo - J.phi) := by rw [sc_sub, sc_S]
    have habs : |ψi - ψj - ((1 : ℤ) : ℝ)| ≤ sc (S - (I.plo - J.phi)) := by
      rw [hD]; push_cast; rw [abs_le]; constructor <;> linarith
    exact ⟨habs, hnn ⟨_, habs⟩, by omega⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hup : ψi - ψj ≤ sc (I.phi - J.plo) := by rw [sc_sub]; linarith
    have hD : sc (I.phi - J.plo + S) = sc (I.phi - J.plo) + 1 := by rw [sc_add, sc_S]
    have habs : |ψi - ψj - ((-1 : ℤ) : ℝ)| ≤ sc (I.phi - J.plo + S) := by
      rw [hD]; push_cast; rw [abs_le]; constructor <;> linarith
    exact ⟨habs, hnn ⟨_, habs⟩, by omega⟩

/-! ### Pair conflict test -/

lemma cosLB_spec (I J : IBox) {ψi ψj : ℝ}
    (hi1 : sc I.plo ≤ ψi) (hi2 : ψi ≤ sc I.phi) (hj1 : sc J.plo ≤ ψj) (hj2 : ψj ≤ sc J.phi)
    (hi01 : 0 ≤ ψi ∧ ψi ≤ 1) (hj01 : 0 ≤ ψj ∧ ψj ≤ 1) :
    sc (cosLB I J) ≤ Real.cos (2 * π * (ψi - ψj)) := by
  unfold cosLB
  rcases hcb : circBound I J with _ | ⟨D, m⟩
  · simp only
    have : sc (-S) = -1 := by rw [show (-S : ℤ) = 0 - S by ring, sc_sub, sc_zero, sc_S]; ring
    rw [this]; exact Real.neg_one_le_cos _
  · simp only
    obtain ⟨hD, hD0, hD2⟩ := circBound_spec hcb hi1 hi2 hj1 hj2 hi01 hj01
    exact le_trans (cosZ_sc hD0 hD2) (cos_turn_le (half_of_two_le hD2) hD)

lemma pairTest_sound {I J : IBox} (h : pairTest I J = true) {si ψi sj ψj : ℝ}
    (hI : InI I si ψi) (hJ : InI J sj ψj) (hi01 : 0 ≤ ψi ∧ ψi ≤ 1) (hj01 : 0 ≤ ψj ∧ ψj ≤ 1) :
    si ^ 2 + sj ^ 2 - 2 * si * sj * Real.cos (2 * π * (ψi - ψj)) < 4 := by
  unfold pairTest at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hIs, hJs⟩, hc⟩ := h
  obtain ⟨hI1, hI2, hI3, hI4⟩ := hI
  obtain ⟨hJ1, hJ2, hJ3, hJ4⟩ := hJ
  have hcos := cosLB_spec I J hI3 hI4 hJ3 hJ4 hi01 hj01
  have hsi : 0 ≤ si := le_trans (sc_nonneg hIs) hI1
  have hsj : 0 ≤ sj := le_trans (sc_nonneg hJs) hJ1
  have hQ := corners_quad hc hI1 hI2 hJ1 hJ2
  have hprod : 0 ≤ si * sj := mul_nonneg hsi hsj
  nlinarith [mul_le_mul_of_nonneg_left hcos hprod]

/-! ### Forbidden arcs of interior points on the boundary circle -/

lemma arc_avoids {ρ : ℤ} {I : IBox} {t : ℤ} (h : arcOK ρ I t = true) (hρ : 0 < ρ) {s ψ a : ℝ}
    (hI : InI I s ψ) (hs2 : s ^ 2 ≤ sc ρ ^ 2 - 4)
    (hd : 4 ≤ sc ρ ^ 2 + s ^ 2 - 2 * sc ρ * s * Real.cos (2 * π * (a - ψ))) :
    Avoids a (arcOf I t) := by
  unfold arcOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hslo, ht0⟩, ht1⟩, hg⟩ := h
  obtain ⟨hI1, hI2, hI3, hI4⟩ := hI
  have hρ' : 0 < sc ρ := sc_pos hρ
  have hslo' : 0 < sc I.slo := sc_pos hslo
  have hs : 0 < s := lt_of_lt_of_le hslo' hI1
  have ht1' : sc t ≤ 1 / 2 := half_of_two_le ht1
  have hgR : (sc ρ ^ 2 + sc I.slo ^ 2 - 4) / (2 * sc ρ * sc I.slo) ≤ sc (cosZ t) := by
    have h' : (((ρ * ρ + I.slo * I.slo - 4 * S * S) * S : ℤ) : ℝ) ≤
        ((cosZ t * (2 * ρ * I.slo) : ℤ) : ℝ) := by
      exact_mod_cast hg
    push_cast at h'
    have hS := S_pos
    have hρ0 : (0 : ℝ) < ρ := by exact_mod_cast hρ
    have hs0 : (0 : ℝ) < I.slo := by exact_mod_cast hslo
    unfold sc
    rw [div_le_iff₀ (by positivity)]
    have key : (((ρ : ℝ) / S) ^ 2 + ((I.slo : ℝ) / S) ^ 2 - 4) =
        ((ρ : ℝ) * ρ + I.slo * I.slo - 4 * S * S) / (S * S) := by
      field_simp
    have key2 : (cosZ t : ℝ) / S * (2 * ((ρ : ℝ) / S) * ((I.slo : ℝ) / S)) =
        (cosZ t * (2 * ρ * I.slo)) / (S * S * S) := by
      field_simp
    rw [key, key2, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h1 : Real.cos (2 * π * (a - ψ)) ≤ (sc ρ ^ 2 + s ^ 2 - 4) / (2 * sc ρ * s) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have h2 : (sc ρ ^ 2 + s ^ 2 - 4) / (2 * sc ρ * s) ≤
      (sc ρ ^ 2 + sc I.slo ^ 2 - 4) / (2 * sc ρ * sc I.slo) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : sc I.slo * s ≤ sc ρ ^ 2 - 4 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hI1) (sub_nonneg.mpr this)]
  have h4 := cosZ_sc ht0 ht1
  have hcos : Real.cos (2 * π * (a - ψ)) ≤ Real.cos (2 * π * sc t) := by linarith
  intro m hm
  have hle := le_abs_sub_int_of_cos_le ht1' hcos m
  simp only [arcOf] at hm
  rw [sc_sub, sc_add] at hm
  have : |a - ψ - m| < sc t := by
    rw [abs_lt]; constructor <;> linarith [hm.1, hm.2]
  linarith

/-- boundary separation from the cosine inequality -/
lemma sep_of_cos {ρ δ : ℤ} (hρ : 0 < ρ) (hδ0 : 0 ≤ δ) (hδ : 2 * δ ≤ S)
    (hδc : (ρ * ρ - 2 * S * S) * S ≤ cosZ δ * (ρ * ρ)) {x y : ℝ}
    (h : 4 ≤ 2 * sc ρ ^ 2 - 2 * sc ρ ^ 2 * Real.cos (2 * π * (x - y))) (m : ℤ) :
    sc δ ≤ |x - y - m| := by
  have hρ' : 0 < sc ρ := sc_pos hρ
  have hcR : 1 - 2 / sc ρ ^ 2 ≤ sc (cosZ δ) := by
    have h' : (((ρ * ρ - 2 * S * S) * S : ℤ) : ℝ) ≤ ((cosZ δ * (ρ * ρ) : ℤ) : ℝ) := by
      exact_mod_cast hδc
    push_cast at h'
    have hS := S_pos
    have hρ0 : (0 : ℝ) < ρ := by exact_mod_cast hρ
    unfold sc
    have key : 1 - 2 / ((ρ : ℝ) / S) ^ 2 = ((ρ : ℝ) * ρ - 2 * S * S) / (ρ * ρ) := by field_simp
    rw [key, div_le_div_iff₀ (by positivity) hS]
    nlinarith
  have h1 : Real.cos (2 * π * (x - y)) ≤ 1 - 2 / sc ρ ^ 2 := by
    have hρ2 : 0 < sc ρ ^ 2 := by positivity
    have : 2 / sc ρ ^ 2 * sc ρ ^ 2 = 2 := by field_simp
    nlinarith
  have h3 := cosZ_sc hδ0 hδ
  exact le_abs_sub_int_of_cos_le (half_of_two_le hδ) (by linarith) m

/-! ### Angular contraction -/

lemma pm_avoids {I J : IBox} {pm : ℤ} (h : pmOK I J pm = true) {si ψi sj ψj : ℝ}
    (hI : InI I si ψi) (hJ : InI J sj ψj)
    (hd : 4 ≤ si ^ 2 + sj ^ 2 - 2 * si * sj * Real.cos (2 * π * (ψi - ψj))) :
    Avoids ψj (I.phi - pm, I.plo + pm) := by
  unfold pmOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hIs, hJs⟩, hp0⟩, hp1⟩, hc⟩ := h
  obtain ⟨hI1, hI2, hI3, hI4⟩ := hI
  obtain ⟨hJ1, hJ2, hJ3, hJ4⟩ := hJ
  have hsi : 0 < si := lt_of_lt_of_le (sc_pos hIs) hI1
  have hsj : 0 < sj := lt_of_lt_of_le (sc_pos hJs) hJ1
  have h1 : Real.cos (2 * π * (ψi - ψj)) ≤ (si ^ 2 + sj ^ 2 - 4) / (2 * si * sj) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have h2 := corners_f hIs hJs hc hI1 hI2 hJ1 hJ2
  have h4 := cosZ_sc hp0 hp1
  have hcos : Real.cos (2 * π * (ψi - ψj)) ≤ Real.cos (2 * π * sc pm) := by linarith
  intro m hm
  have hle := le_abs_sub_int_of_cos_le (half_of_two_le hp1) hcos (-m)
  simp only at hm
  rw [sc_sub, sc_add] at hm
  push_cast at hle
  have : |ψi - ψj - -(m : ℝ)| < sc pm := by
    rw [abs_lt]; constructor <;> linarith [hm.1, hm.2]
  linarith

/-! ### Shrinking an angle interval by an avoided arc -/

lemma sc_add_mulS (z m : ℤ) : sc (z + m * S) = sc z + m := by
  rw [sc_add]; unfold sc; push_cast; field_simp [S_pos.ne']

lemma shrinkLo1_le {p : ℤ × ℤ} {x : ℝ} (hav : Avoids x p) (m : ℤ) {lo : ℤ} (hx : sc lo ≤ x) :
    sc (shrinkLo1 p (m * S) lo) ≤ x := by
  unfold shrinkLo1
  split_ifs with hc
  · have h1 : sc (p.1 + m * S) < sc lo := sc_lt_iff.mpr hc.1
    rw [sc_add_mulS] at h1
    rw [sc_add_mulS]
    by_contra hlt
    push Not at hlt
    exact hav m ⟨by linarith, hlt⟩
  · exact hx

lemma le_shrinkHi1 {p : ℤ × ℤ} {x : ℝ} (hav : Avoids x p) (m : ℤ) {hi : ℤ} (hx : x ≤ sc hi) :
    x ≤ sc (shrinkHi1 p (m * S) hi) := by
  unfold shrinkHi1
  split_ifs with hc
  · have h2 : sc hi < sc (p.2 + m * S) := sc_lt_iff.mpr hc.2
    rw [sc_add_mulS] at h2
    rw [sc_add_mulS]
    by_contra hlt
    push Not at hlt
    exact hav m ⟨hlt, by linarith⟩
  · exact hx

lemma shrinkLo_le {p : ℤ × ℤ} {x : ℝ} (hav : Avoids x p) {lo : ℤ} (hx : sc lo ≤ x) :
    sc (shrinkLo p lo) ≤ x := by
  unfold shrinkLo
  have h1 := shrinkLo1_le hav (-1) hx
  rw [show (-1 : ℤ) * S = -S by ring] at h1
  have h2 := shrinkLo1_le hav 0 h1
  rw [show (0 : ℤ) * S = 0 by ring] at h2
  have h3 := shrinkLo1_le hav 1 h2
  rw [show (1 : ℤ) * S = S by ring] at h3
  exact h3

lemma le_shrinkHi {p : ℤ × ℤ} {x : ℝ} (hav : Avoids x p) {hi : ℤ} (hx : x ≤ sc hi) :
    x ≤ sc (shrinkHi p hi) := by
  unfold shrinkHi
  have h1 := le_shrinkHi1 hav 1 hx
  rw [show (1 : ℤ) * S = S by ring] at h1
  have h2 := le_shrinkHi1 hav 0 h1
  rw [show (0 : ℤ) * S = 0 by ring] at h2
  have h3 := le_shrinkHi1 hav (-1) h2
  rw [show (-1 : ℤ) * S = -S by ring] at h3
  exact h3

end CirclePacking
