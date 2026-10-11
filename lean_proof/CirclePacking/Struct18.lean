import CirclePacking.Surv18Err
import CirclePacking.N18CoreCheck

/-!
# The 18-circle structures: exact points and consistency with their local-uniqueness data

* `structPt T p`: the exact point with label `p` of the structure `T` (interior points, then boundary circles),
  `structQ T` its coordinate list; `structPt_eval`: polar form.
* `labOK T k`: for every position `jc ≥ 1` of the centre among the box indices, `tLab T jc` permutes `0..k-1`.
* `structOK T L k`: the structure and the local-uniqueness data `L` fit together (sizes, boundary labels, gauge,
  uniqueness radius, labelling).
-/

open Real

namespace CirclePacking

/-- the radius of a code, exactly -/
def radQ (c : ℕ) : Q23 := if c = 0 then 0 else if c = 1 then ringQ else s2Q

lemma radQ_eval (c : ℕ) : (radQ c).eval = radOf c := by
  unfold radQ radOf
  split_ifs
  · exact Q23.eval_zero
  · simp [Q23.eval, ringQ]
  · simp [Q23.eval, s2Q]

/-- the exact point with label `p` -/
def structPt (T : Struct18) (p : ℕ) : Q23 × Q23 :=
  if p < T.k then pointQ (radQ (T.code p)) (T.ang p) else pointQ rho19Q (T.bnd.getD (p - T.k) 0)

/-- the coordinate list `x₀, y₀, x₁, y₁, …` -/
def structQ (T : Struct18) : List Q23 :=
  (List.range (T.k + T.bnd.length)).flatMap (fun p => [(structPt T p).1, (structPt T p).2])

lemma flatMap_pair_getD {α : Type*} (f g : ℕ → α) (d : α) (n p : ℕ) (hp : p < n) :
    ((List.range n).flatMap (fun q => [f q, g q])).getD (2 * p) d = f p ∧
    ((List.range n).flatMap (fun q => [f q, g q])).getD (2 * p + 1) d = g p := by
  induction n generalizing p with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have hlen : ((List.range n).flatMap (fun q => [f q, g q])).length = 2 * n := by
      simp [List.length_flatMap]; ring
    by_cases h : p < n
    · obtain ⟨h1, h2⟩ := ih p h
      constructor
      · rw [List.getD_append _ _ _ _ (by rw [hlen]; omega)]; exact h1
      · rw [List.getD_append _ _ _ _ (by rw [hlen]; omega)]; exact h2
    · have hp' : p = n := by omega
      subst hp'
      constructor
      · rw [List.getD_append_right _ _ _ _ (by rw [hlen])]; simp [hlen]
      · rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega)]; simp [hlen]

lemma structQ_getD (T : Struct18) {p : ℕ} (hp : p < T.k + T.bnd.length) :
    (structQ T).getD (2 * p) 0 = (structPt T p).1 ∧ (structQ T).getD (2 * p + 1) 0 = (structPt T p).2 :=
  flatMap_pair_getD _ _ 0 _ p hp

/-- the point with label `p`, as a complex number -/
noncomputable def structC (T : Struct18) (p : ℕ) : ℂ := ⟨(structPt T p).1.eval, (structPt T p).2.eval⟩

lemma structC_int (T : Struct18) {p : ℕ} (hp : p < T.k) :
    structC T p = polar (radOf (T.code p)) ((T.ang p : ℕ) / 24 : ℝ) := by
  unfold structC structPt
  rw [if_pos hp, pointQ_eval, radQ_eval]

lemma structC_bnd (T : Struct18) {p : ℕ} (hp : T.k ≤ p) :
    structC T p = polar ρ19 ((T.bnd.getD (p - T.k) 0 : ℕ) / 24 : ℝ) := by
  unfold structC structPt
  rw [if_neg (by omega), pointQ_eval, rho19Q_eval]

lemma coreC_structQ (T : Struct18) {p : ℕ} (hp : p < T.k + T.bnd.length) :
    coreC (structQ T) (2 * p) = (structC T p).re ∧ coreC (structQ T) (2 * p + 1) = (structC T p).im := by
  obtain ⟨h1, h2⟩ := structQ_getD T hp
  exact ⟨by simp only [coreC, h1, structC], by simp only [coreC, h2, structC]⟩

/-! ### Consistency checks -/

/-- the labelling of box indices by structure labels is a permutation of `0..k-1`, for every centre position -/
def labOK (T : Struct18) (k : ℕ) : Bool :=
  (List.range k).all (fun jc => decide (jc = 0) ||
    ((List.range k).all (fun i => decide (tLab T jc i < k)) &&
     (List.range k).all (fun i => (List.range k).all (fun j => !(decide (tLab T jc i = tLab T jc j)) || decide (i = j)))))

/-- the structure `T` with `k` interior points fits the local-uniqueness data `L` -/
def structOK (T : Struct18) (L : LUData) (k : ℕ) : Bool :=
  decide (T.k = k) && decide (k ≤ 17) && decide (T.bnd.length = 18 - k) && decide (L.N = 18) &&
  decide (L.bnd = (List.range (18 - k)).map (· + k)) && decide (L.gauge = 1) && decide (T.R2 ≤ L.R2) &&
  decide (T.code 0 ≠ 0) && decide (T.ang 0 = 0) && decide (T.code T.centre = 0) && labOK T k &&
  T.bnd.all (fun b => decide (b < 24))

end CirclePacking
