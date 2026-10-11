import CirclePacking.Struct18
import CirclePacking.N18Core
import C18Tmpl

/-!
# The hexagon cores, from the structure `sHex`

`hexPt m p`: label `p < 7` is the interior point `p` of `sHex` (ring circles, then the centre); label `7 + s`
(`s < 10`) is the boundary circle of slot `s` of the core with short window `m`
(`2 · hexWin m (s / 2) + s % 2` among the twelve lattice slots).  `hexLU m` is the local-uniqueness data of that
core (`N18Core.lean`); the exact points satisfy it (`hexG_exact`, `hexG_near`).
-/

namespace CirclePacking

/-- the local-uniqueness data of the hexagon core with short window `m` -/
def hexLU (m : ℕ) : LUData := [hexLU0, hexLU1, hexLU2, hexLU3, hexLU4, hexLU5].getD m hexLU0

/-- the lattice slot of slot `s` of the core with short window `m` -/
def hexSlot (m s : ℕ) : ℕ := 2 * hexWin m (s / 2) + s % 2

/-- the exact point with label `p` of the core with short window `m` -/
def hexPt (m p : ℕ) : Q23 × Q23 :=
  if p < 7 then structPt sHex p else pointQ rho19Q (sHex.bnd.getD (hexSlot m (p - 7)) 0)

/-- its coordinate list -/
def hexQg (m : ℕ) : List Q23 := (List.range 17).flatMap (fun p => [(hexPt m p).1, (hexPt m p).2])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hexLU0_ok : hexLU0.ok = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hexLU1_ok : hexLU1.ok = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hexLU2_ok : hexLU2.ok = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hexLU3_ok : hexLU3.ok = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hexLU4_ok : hexLU4.ok = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hexLU5_ok : hexLU5.ok = true := by decide +kernel

theorem hexLU_ok : ∀ m < 6, (hexLU m).ok = true := by
  intro m hm
  interval_cases m
  exacts [hexLU0_ok, hexLU1_ok, hexLU2_ok, hexLU3_ok, hexLU4_ok, hexLU5_ok]

/-- the shapes of the six data sets, and their uniqueness radii -/
theorem hexLU_shape : ∀ m < 6, (hexLU m).N = 17 ∧ (hexLU m).bnd = [7, 8, 9, 10, 11, 12, 13, 14, 15, 16] ∧
    (hexLU m).gauge = 1 ∧ hexR2s.getD m 0 ≤ (hexLU m).R2 := by decide +kernel

/-- the structure `sHex` -/
theorem sHex_shape : sHex.k = 7 ∧ labOK sHex 7 = true ∧ sHex.code 0 ≠ 0 ∧ sHex.ang 0 = 0 ∧
    sHex.code sHex.centre = 0 ∧ sHex.bnd.length = 12 := by decide +kernel

lemma hexPt_int (m : ℕ) {p : ℕ} (hp : p < 7) : hexPt m p = structPt sHex p := by
  simp [hexPt, hp]

lemma hexQg_getD (m : ℕ) {p : ℕ} (hp : p < 17) :
    (hexQg m).getD (2 * p) 0 = (hexPt m p).1 ∧ (hexQg m).getD (2 * p + 1) 0 = (hexPt m p).2 :=
  flatMap_pair_getD _ _ 0 _ p hp

/-- the point with label `p` of the core with short window `m`, as a complex number -/
noncomputable def hexC (m p : ℕ) : ℂ := ⟨(hexPt m p).1.eval, (hexPt m p).2.eval⟩

lemma hexC_int (m : ℕ) {p : ℕ} (hp : p < 7) :
    hexC m p = polar (radOf (sHex.code p)) ((sHex.ang p : ℕ) / 24 : ℝ) := by
  have h7 : sHex.k = 7 := sHex_shape.1
  unfold hexC
  rw [hexPt_int m hp]
  exact structC_int sHex (by rw [h7]; exact hp)

lemma hexC_bnd (m s : ℕ) :
    hexC m (7 + s) = polar ρ19 ((sHex.bnd.getD (hexSlot m s) 0 : ℕ) / 24 : ℝ) := by
  unfold hexC hexPt
  rw [if_neg (by omega), show 7 + s - 7 = s by omega, pointQ_eval, rho19Q_eval]

lemma coreC_hexQg (m : ℕ) {p : ℕ} (hp : p < 17) :
    coreC (hexQg m) (2 * p) = (hexC m p).re ∧ coreC (hexQg m) (2 * p + 1) = (hexC m p).im := by
  obtain ⟨h1, h2⟩ := hexQg_getD m hp
  exact ⟨by simp only [coreC, h1, hexC], by simp only [coreC, h2, hexC]⟩

theorem hexG_exact : ∀ m < 6, coreExactOK (hexLU m) (hexQg m) = true := by decide +kernel
theorem hexG_near : ∀ m < 6, coreNearOK23 (hexLU m) (hexQg m) = true := by decide +kernel

end CirclePacking
