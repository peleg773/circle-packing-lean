# Skeptic report: claimed computer-assisted optimality proof for n = 15 and n = 16

Referee: independent adversarial review, 2026-10-10.
Scope: `proof_attempt.md`, `lemmas.md`, `experiments/{ringbb_rig, rigmath, ringbb2, local_cert,
verify_final_arb, verify_L4, final_check, soundness_test, soundness_random}.py`,
`known_packings/local_certificate_n15.json` and `local_certificate_n16.json`, and the survivor files in `out/`.
No project file was modified. All tests ran single-process on a copy of the code in the session scratchpad.

## Verdict

**Not a proof yet.** The theorem statements at the top of `proof_attempt.md` claim results that the
computations do not yet support. The rigorous branch and bound (B&B) has not been run, or has left no
evidence, for most of the required k (F1). The runs that are reported as done left no auditable record (S1).

Every mathematical argument and every rigorous code path I checked holds up: L1, L2, the exact reduction,
L3 (statement), L4/L5 including the rho_test monotonicity, L6, L7 including the torque argument and the
constant K, the assembly, `bmax_rig`, `contract_rig`, P1, P2a, P4, the `rigmath` enclosures, and
`verify_final_arb`. I tried to break each of them, both analytically and by computation. **I found no FATAL
mathematical or coding error in the parts that exist.** The remaining problems are about completeness and
auditability, plus a few latent bugs and steps that are not fully rigorous. Each one is listed below.

---------------------------------------------------------------------------------------------------------
## FATAL

### F1. The theorems are stated as proven, but the rigorous computation is incomplete
`proof_attempt.md:10-20` (Theorems 15 and 16) against `proof_attempt.md:77-83` (gap list).
* **n = 16** needs rigorous runs for k = 5..11. Only k = 5, 6, 7 are claimed done. **k = 8, 9, 10, 11 are
  float-only.** The float code is not rigorous: it uses libm and EPS margins, and it uses the reduction
  rule P3 (see M6).
* **n = 15** needs rigorous runs for k = 5..10. **None has been run.** The section 5 neighbourhood check for
  n = 15 can only have used `out/surv_n15_k5.npy`, which is the output of the **float** B&B
  (`ringbb2.py`), not of `ringbb_rig.py`.
* Until every k in the required range finishes rigorously, with zero survivors for k >= 6 (or survivors that
  are handled) and certified k = 5 survivors, neither theorem is established. The assembly in section 6 uses
  "Yhat has k = 5 interior points lying in a survivor box", and that sentence is unproven for k >= 8
  (n = 16) and for every k (n = 15).

---------------------------------------------------------------------------------------------------------
## SERIOUS

### S1. The rigorous runs reported as done cannot be audited
`ringbb_rig.py:359-369` only prints to stdout and saves a `.npy` file only when there are survivors. In
`out/` there is **no log of any rigorous run**: the only logs are `bb2_*.log` (float) and a one-line
`bb_n16_k9_v1.log`. So the record lacks:
* the rho_test, tol, presplit target and code version used for n = 16, k = 5, 6, 7;
* the counts of `unfinished`, `overflow` (reasons[0]) and survivors;
* any proof that k = 6 and k = 7 ran to completion. A missing `rigsurv_n16_k6.npy` is equally consistent
  with "0 survivors" and with "never run" or "crashed".

I could only check that `rigsurv_n16_k5.npy` is consistent with rho_test = 3.6154255948732. Re-applying
`box_ok_rig` at that rho_test to all 1575 boxes kept every box and contracted none further.

Fix: for each (n, k), save a machine-readable record with the parameters, `rigorous_params` output, counts,
unfinished, overflow, git hash or source hashes, and the survivors. Make `verify_final_arb` refuse to run
unless overflow == 0 and unfinished == 0.

---------------------------------------------------------------------------------------------------------
## MINOR (latent bugs, steps that are not fully rigorous, documentation)

### M1. `verify_final_arb.py`: a failed arc construction is silently counted as an empty box
At `verify_final_arb.py:111`, `allowed_arcs_exact` returns only arcs whose start lies in [0, P).
* If **no certainly-forbidden arc exists** (every theta_lo is 0, or every shrunk arc is inverted), there are
  no merged segments, so `allowed = []`. `placements` then returns `[]`, and `main` treats the box as
  containing no feasible configuration and `continue`s (`verify_final_arb.py:218-220`).
* In reality such a box is feasible: n-k points fit on a free circle.
* The same thing happens in a contrived case: tiny forbidden arcs (< 2e-12) whose right end falls in
  [P, P + 1e-12). Their shifted copies are inverted, so no allowed arc starts in [0, P).

This has no effect on the current data: `nopl = 0` for all 1575 n = 16 boxes and all 2217 n = 15 boxes
(re-run). The function should treat "no forbidden arcs" as the full circle, and any `nopl > 0` should
trigger a separate rigorous emptiness argument, not a silent skip.

### M2. `verify_final_arb.py` is labelled RIGOROUS but has non-rigorous steps
These are tiny and the margin is about 5x, but they are real:
* (a) At line 175, `float(arb_lo(lo))` and `float(arb_hi(hi))` round to nearest. An odd multiple of pi up
  to half an ulp inside the true angle interval can be missed, which changes cm by O(1e-31).
* (b) At lines 184 and 190, `min(...)` and `vh > best` are applied to arb balls that may overlap.
* (c) The whole boundary term (lines 232-248) is computed in double precision, with an ad hoc `+1e-12` and
  a `(1+1e-9)` factor. The `round()` lifting uses the float value of 2*pi.
* (d) At line 252, the final comparison uses `float(thr)`, which rounds to nearest.

Re-run results: worst D = 1.656e-4 against a threshold of 8.711e-4 (n = 16), and 2.118e-4 against 1.084e-3
(n = 15, float survivors). The conclusion is safe, but these steps should be done with arb or `Fraction`.

### M3. `verify_L4.py` uses theta outside the range where it is monotone
At line 19, `hi = RI.mid()+RI.rad()` can lie above R_I, where theta is *decreasing*. So `theta(s2)` at line
44 is not quite an upper bound of theta on the box: the error is O(rad^2) ~ 1e-76. The selection of `fm`
also compares overlapping balls. Neither matters, because L4 is certified with one box and margins of
0.0650 rad (n = 16) and 0.0724 rad (n = 15). Both values reproduced. Clamp `hi` to R_I's lower end, or use
theta(R_I) for boxes that contain R_I.

### M4. The written proof of L3 (`lemmas.md:46-56`) is garbled
Part (ii) moves x_1 "clockwise until it ... comes within delta of x_N, then x_2, ...". As written this is
not a proof. The statement is true, and a one-line argument proves it. Take an optimal placement in which
x_i lies in the allowed arc [L_i, R_i]. Rotate the whole placement by -t* with t* = min_i (x_i - L_i).
Distances do not change, every point stays in its arc, and one point lands on a left endpoint. The case
A = full circle is handled separately (the code does this). Part (i) ("greedy stays ahead") is fine.

### M5. Documentation is inconsistent
* `lemmas.md:58` labels L4 "rigorous check: TODO", but `verify_L4.py` exists and passes.
* `lemmas.md:99` labels L8 "float; arb re-check TODO", while `proof_attempt.md:61-63` claims the arb
  verification.
* `proof_attempt.md:79` says the n = 16 k = 11 float run is "running", but `out/bb2_n16_k9_11.log` shows it
  finished.
* `proof_attempt.md:42-43` says P1's max distance is "also used for rigorous angular contraction". In fact
  `contract_rig` uses a lower bound on theta_II (`phimin_lo_rig`), not the max distance.
* `proof_attempt.md:72-75` (uniqueness) says "pushed". The argument is only valid if "pushed" means
  *actually moved* (|y| < rho*). Points with R_I < |y| = rho* are "pushed" under L1's definition but do not
  move, and the f'-argument does not apply to them. With the corrected wording the argument holds: I checked
  that both contact graphs are connected.

### M6. Float runs use the reduction rule P3, which the rigorous code does not have
`ringbb2.py:287-290` together with `_worker` at lines 393-396 (`use_reduction=True`).
* The float "empty" results for k >= 6 used P3: 58 boxes for n = 16 k = 11, and 14 for n = 15 k = 10. P3
  is absent from `box_ok_rig` (correctly), so the float results do not predict that the rigorous runs will
  close. Those regions must be cut by P1, P2, P2a or P4 instead.
* **Do not add P3 to the rigorous code** without rewriting the uniqueness argument. P3 swaps Y for a
  *different* configuration Y' with fewer interior points, so Y' ≅ c* does not imply Y ≅ c*. It is valid
  for the strict optimality part only.

### M7. Surviving boxes can be dropped from the output
At `ringbb_rig.py:289-293`, when the survivor array is full, the box is dropped and only `reasons[0]` is
incremented. Nothing downstream enforces overflow == 0. This was not triggered here (1575 survivors), but
it must be a hard failure.

### M8. `local_cert.py` does not prove y_m != 0
At line 154, the torque argument for the dropped equation needs y_m != 0. The code only prints it: the
values are -0.9939 (n = 16) and 0.9659 (n = 15), so it obviously holds, but it should be asserted with an
arb comparison.

### M9. numba `cache=True` can run stale code
numba's cache does not see changes in other modules. `rigmath.dn/up` are inlined into `ringbb_rig`, and
`ringbb2` functions are called from `ringbb_rig`. The current cache timestamps are consistent: everything
was recompiled at 23:28-23:29, after the last edits of `rigmath.py` (23:26) and `ringbb2.py` (23:11). But
editing `rigmath.py` later without touching `ringbb_rig.py` would silently run stale code. For certified
runs, disable the cache or clear `__pycache__`.

### M10. The soundness tests check too little
`soundness_test.py:75` and `soundness_random.py:63` check only the return code of `box_ok_rig`. They do not
check that the box, after the *in-place* P4 and contraction, still contains the feasible point. I ran this
check (below): 0 losses.

### M11. The proof depends on literature the authors did not read
The values are correct, but the proof is conditional on published theorems:
* rho_10 (Pirl 1969, "not accessed" according to `literature.md`);
* rho_11 (Melissen 1994, abstract only);
* rho_12 (Fodor 2000).

They enter in two places:
* **P4:** s_j >= rho_{k-j}.
* **The k-range:**
  * n = 16 needs k <= 11, which uses rho_12 = 3.029602 > R_I(rho_test) = 3.011860 (margin 0.0177).
  * n = 15 needs k <= 10, which uses rho_11 = 2.923804 > 2.898268.

There is no fallback, because k = 12 (n = 16) and k = 11 (n = 15) are never searched. The values used are
valid lower bounds:
* 2.8130250 < 2.8130256313981244 (R_10 - 1);
* 3.0296 < 3.0296019301161835 (R_12 - 1);
* the others are exact closed forms, bracketed in arb.

---------------------------------------------------------------------------------------------------------
## Checked and found correct (analytically and/or by computation)

1. **L1 (push-out).** The proof is correct, including the case of several points pushed in sequence.
   Earlier pushed points have |c| = rho <= rho, and the inequality t0^2 > rho^2 - 4 >= s^2 - 4 still holds.
   * Two points cannot share a ray outside R_I, since their distance would be < rho - R_I < 2.
   * The origin is never pushed.
   * The one-point strict version used for uniqueness also holds.
2. **The reduction is exact and the interior/boundary split is exhaustive.** I found no missing constraint.
   L2 is the law of cosines; the arc is open; theta = 0 exactly when s <= rho - 2. Monotonicity in rho holds
   for theta, delta_B and R_I. Moving boundary points out radially from rho* to rho_test keeps every
   constraint, so a B&B run at rho_test >= rho* is sound. P2a uses L4 and L5 at rho_test, and L4 was
   verified at rho_test. Both rho_test values exceed rho*: by 6.16e-15 (n = 16) and 5.75e-15 (n = 15).
3. **Canonical form.** It is a valid fundamental domain.
   * s_0 >= rho_5 > 0, so psi_0 is defined.
   * Reflection keeps psi_0 = 0.
   * Ties in radius are harmless, because existence of a canonical form is all that is needed.
4. **`bmax_rig` is an upper bound.**
   * Every left endpoint of the true allowed set A' is some hi_j.
   * A start is skipped only if it lies strictly inside a sub-arc of the true arcs.
   * Lifted arcs are subsets of the true ones even though 2*pi is uncertain.
   * The greedy steps by induction give z <= the exact positions.
   * The limit is rounded up.

   Tests:
   * **Computation:** 19,800 configuration-in-box tests against an independent mpmath exact Bmax: 0
     under-counts. Boxes included wrap-around at 0 and 2*pi and k = 1..8, at both rho_test values.
   * **Float filter:** `bmax_box` in 6,000 tests: 0 under-counts.
5. **`contract_rig`.** The excluded set (phi_a - pm, plo_a + pm), with the shifts -1, 0, +1 shrunk safely,
   is infeasible for every psi_a in the box. There is no off-by-one, and the in-place updates are
   consistent. In 5,970 random feasible configurations and boxes, nothing was pruned and nothing was lost
   by contraction.
6. **End-to-end.** I ran 80 rigorous mini-B&B runs (`run_bb_rig`, including splitting) on small boxes
   around feasible local optima with n = 15..18 and k = 2..9. The feasible point always survived.
7. **`rigmath`.** No enclosure failure in:
   * 180k acos tests (including +-1, +-0, subnormals, and points near +-1 to 1e-17);
   * 100k cos tests (including multiples of pi/2 +- 1e-15);
   * 60k `cos_min_lo` tests (including endpoints next to odd multiples of pi);
   * 100k imul, isqr and idiv tests.

   Coefficient brackets were verified, and the arcsine coefficients are decreasing (needed for the tail
   bound). For `theta_lo_rig`, `phimin_lo_rig` and `maxdist2_hi_rig`, 40k tests showed no failure.
   * **Corner maximum of f.** With f = (s^2+t^2-4)/(2st), the second derivative in s is
     (t^2-4)/(s^3 t). So f is convex in s when t >= 2, and increasing in s when t < 2 (since
     f_s = (s^2-t^2+4)/(2s^2 t) > 0). Either way the maximum is at a corner.
   * **Monotonicity of theta.** With g(s) = (s^2 + rho^2 - 4)/(2 s rho), g'(s) = (s^2-rho^2+4)/(2s^2 rho)
     < 0 on (0, R_I). So theta = arccos(g) is increasing there.
8. **L4 and L5.** The disjointness argument is correct. L4 re-verified in arb at both rho_test values.
9. **L7.**
   * The inequality chain, the rotation gauge (delta . J x* = 0), Q <= 2 eps^2 and K are correct.
   * Ball arithmetic on the Krawczyk box encloses lambda, mu and sigma at the exact x*.
     `arb_mat.solve` is the rigorous LU solver.
   * J x* lies in ker L, and the u u^T term certifies that it spans the whole kernel.
   * The torque identity sum_i p_i x r_i = 0 holds for any lambda, mu, so the dropped equation is implied
     whenever y_m != 0.
   * `local_cert.py` re-run for n = 15 and n = 16 reproduces both JSON certificates *exactly*.
10. **Assembly.** The scaling (lambda > 1), L1 at rho*, L7 applied to Yhat/rho*, and the contradiction
   through interior-interior contacts are all valid. Both contact graphs are connected.
11. **Section 5.** I re-ran the `verify_final_arb` logic on all survivors (results in M2); nopl = 0. Every
   tie-consistent canonical form of c* lies in a survivor box: 4 of 4 for n = 16, 120 of 120 for n = 15.
   The n = 15 survivors still come from the float B&B (F1).
12. **Constants.**
   * The closed form for rho*_15 matches the certificate to 4e-38.
   * 41 d^8 - 200 d^6 + 285 d^4 - 150 d^2 + 25 = -5e-60 at d_15.
   * The rho*_16 and d*_16 digits match.
   * 2*pi/delta_B = 11.210 (n = 16) and 10.910 (n = 15), giving k >= 5.
13. **B&B bookkeeping.** presplit never drops a box. Hitting the stack cap marks the box as a survivor
   rather than dropping it. The max_boxes limit is reported as "unfinished". The survivor overflow is
   handled as in M7.

## Reproduction
The test scripts are in the session scratchpad, in `scratchpad/tests/`:
* `t_rigmath.py`;
* `t_bmax.py` and `t_bmax_float.py`;
* `t_contract.py`;
* `t_e2e.py`;
* `t_geom.py`;
* `t_vfa_sample.py`.

They import a copy of `experiments/`.
