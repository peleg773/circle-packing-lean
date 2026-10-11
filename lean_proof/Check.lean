import CirclePacking.Final
import CirclePacking.Final16
import CirclePacking.Final18

/-! Prints the statements and the axioms they depend on:  `lake env lean Check.lean` -/

#check @CirclePacking.circle_packing_15
#check @CirclePacking.circle_packing_15_euclidean
#check @CirclePacking.circle_packing_15_iff
#print axioms CirclePacking.circle_packing_15
#print axioms CirclePacking.circle_packing_15_euclidean
#print axioms CirclePacking.circle_packing_15_iff

/-! n = 15: the explicit configuration `optimal15` (`Exact15.lean`): five inner centres on a regular pentagon,
ten centres on the boundary circle.  That it is the certified optimum uses only the standard axioms. -/

#print CirclePacking.optimal15
#print CirclePacking.Opt15.ρ
#print CirclePacking.Opt15.r
#print CirclePacking.Opt15.α
#print CirclePacking.Opt15.P
#print axioms CirclePacking.optimal15_eq_Cs

#check @CirclePacking.circle_packing_16
#check @CirclePacking.circle_packing_16_euclidean
#check @CirclePacking.circle_packing_16_iff
#print axioms CirclePacking.circle_packing_16
#print axioms CirclePacking.circle_packing_16_euclidean
#print axioms CirclePacking.circle_packing_16_iff

/-! n = 16: every definition the statement uses.  `R16` comes from the largest real root `q16` of the
degree-90 polynomial `H16`; `optimal16` is built from `q16` (`Opt16`). -/

#print CirclePacking.R16
#print CirclePacking.q16
#print CirclePacking.H16
#print CirclePacking.ZPoly
-- `ZPoly.toPoly [a₀, a₁, …] = a₀ + X * toPoly [a₁, …]`, so `H16 = ∑ H16coeffs[i] Xⁱ`:
#check @CirclePacking.ZPoly.toPoly.eq_1
#check @CirclePacking.ZPoly.toPoly.eq_2
#check @CirclePacking.H16_coeff
#check @CirclePacking.H16_natDegree
-- the 91 coefficients of `H16`, constant term first (a plain display of the definition `H16coeffs`)
#eval IO.println (toString CirclePacking.H16coeffs)
#print CirclePacking.optimal16
#print CirclePacking.Opt16.ρ
#print CirclePacking.Opt16.θ
#print CirclePacking.Opt16.B
#print CirclePacking.Opt16.a
#print CirclePacking.Opt16.d
#print CirclePacking.Opt16.D
#print CirclePacking.Opt16.b
#print CirclePacking.Opt16.c
#check @CirclePacking.q16_bounds
#check @CirclePacking.R16_bounds

/-! n = 16: everything except the lower bound uses only the standard axioms (no certificate axioms): that
`q16` is the largest root, that `optimal16` is the certified optimum `c*` and a packing at radius `R16`, and the
decimal brackets. -/

#print axioms CirclePacking.q16_isGreatest
#print axioms CirclePacking.optimal16_eq_C16
#print axioms CirclePacking.cstar16_packing
#print axioms CirclePacking.R16_eq
#print axioms CirclePacking.H16_natDegree
#print axioms CirclePacking.q16_bounds
#print axioms CirclePacking.R16_bounds

/-! n = 18 -/

#check @CirclePacking.circle_packing_18
#check @CirclePacking.circle_packing_18_euclidean
#check @CirclePacking.circle_packing_18_iff
#print axioms CirclePacking.circle_packing_18
#print axioms CirclePacking.circle_packing_18_euclidean
#print axioms CirclePacking.circle_packing_18_iff

/-! n = 18: every definition the statement uses (`polar r t` is the point at distance `r` and angle `t`
turns).  That `optimal18` is a packing at radius `R18` uses only the standard axioms. -/

#print CirclePacking.R18
#print CirclePacking.optimal18
#print CirclePacking.polar
#print axioms CirclePacking.optimal18_packing

/-! What a certificate axiom states (three examples; every `…native_decide.ax_1_1` axiom has this form:
one closed Boolean computation from `CirclePacking/Cert/` evaluates to `true`). -/

#print CirclePacking.n15_k10_c3._native.native_decide.ax_1_1
#print CirclePacking.n16_k10_c3._native.native_decide.ax_1_1
#print CirclePacking.n18_k7_c3._native.native_decide.ax_1_1

/-! Cross-check of compiled against kernel evaluation: the kernel itself (no compiled code) evaluates the
runs that close at the root and one small search, with the same definitions the certificates use.  (The large
searches exceed the kernel's recursion limit; they are evaluated only by `native_decide`.) -/

set_option maxRecDepth 100000 in
example : CirclePacking.n15small = true := by decide +kernel

set_option maxRecDepth 100000 in
example : CirclePacking.n16small = true := by decide +kernel

set_option maxRecDepth 100000 in
example : CirclePacking.n18small = true := by decide +kernel

set_option maxRecDepth 100000 in
example : CirclePacking.checkRun (CirclePacking.Prb 8 3) (fun _ => false) 400 = true := by decide +kernel
