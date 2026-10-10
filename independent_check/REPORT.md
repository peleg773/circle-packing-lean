# Independent check of the 15-circle claims C1 and C2

(Report text produced by the independent re-implementation agent; saved to this file by the main agent because the
subagent's environment could not write report files.  All code in this folder was written from scratch by that
agent, without reading `experiments/`.)

Environment: Python 3.10.9, numpy 2.2.6, numba 0.68.0, scipy 1.15.3, python-flint 0.9.0 (arb). At most 4 of the
agent's processes were busy at any time; another 40-process job shared the machine, so wall-clock times are pessimistic.

## 0. Verdict
- **C1 is CONFIRMED.** For k = 6..10 there are 0 unresolved boxes at rho_test in the float64 B&B with safety margins,
  and in a separate fully rigorous B&B (arb ball arithmetic plus exact rationals), both with and without F4.
- **C2 is CONFIRMED, with a stronger bound.** Every admissible k = 5 interior set lies within 3.46e-6 (rigorous run,
  tolerance 1e-6) of the regular pentagon of circumradius 1/sin 36°.
- No discrepancy was found.

## 1. Constants (arb, 200-bit)
- rho_test = 3.52135696470616998965…, rho* = 3.52135696470616424091…, rho_test − rho* = 5.7487e-15.
- R_I = 2.8982675640604, rho − 2 = 1.5213569647062, δ_B = 0.57588791899071; 11·δ_B = 6.3348 > 2π, so k ≥ 5.
- slack_m = 2π − m·δ_B: 0.524306 (m = 10), 1.100194 (9), 1.676082 (8), 2.251970 (7), 2.827858 (6), 3.403746 (5).
- θ(R_I) = arcsin(2/rho) = 0.6040286 (maximum of θ); θ(r5) = 0.3403746; 5·(2θ(r5) − δ_B) = 0.5243061 = slack_10
  (the pentagon is tight).
- F1 re-derived: whenever f(t) = |t·u − c_j|² equals 4, f'(t) = (t² − |c_j|² + 4)/t > 0 for t > R_I.
- F2: stable form sin²(θ/2) = (s − (rho − 2))(2 + rho − s)/(4·rho·s); θ increasing on (rho − 2, R_I].

## 2. Canonical form
- Point 0 has maximal radius and sits at angle 0; points 1..k−1 are ordered by angle in [0, 2π]; if
  psi_1 + psi_{k−1} > 2π, reflect (psi → 2π − psi), which gives psi_1 + psi_{k−1} ≤ 2π.
- Every admissible configuration has such a representative, so the root box covers everything.

## 3. Rules (each removes only parts that provably contain no admissible configuration)
- **R1, order and counting:** s_i ≤ s_0, angle order, reflection inequality; s_0 ≥ r_k; counting (F4): the centres
  with s_i < r_n lie in a closed disk of radius < r_n, so there are at most n − 1 of them; if n − 1 boxes certainly
  have s < r_n, every other box gets s_lo ≥ r_n (r_n of F4 minus 1e-9).
- **R2, pair too close:** exact maximum of |P_i − P_j|² over the pair of boxes (max over the 4 radius corners of
  s_i² + s_j² − 2 s_i s_j cmin); prune if < 4.
- **R3, angular exclusion:** |Δ| ≥ D = 2 arcsin(√h_min) with h = (4 − (s_i − s_j)²)/(4 s_i s_j) minimised at a corner;
  the arc (psi_j,hi − D, psi_j,lo + D) + 2πZ is cut from the angle interval of i when it covers an end.
- **R4, radial exclusion:** for fixed s_i the maximum distance to box j is the larger of two corner quadratics; the
  open interval of s_i where both are < 4 is cut from [s_lo, s_hi] when it covers an end.
- **R5, excess lemma:** with e(s) = (2θ(s) − δ_B)⁺, Σ_i e(s_i) ≤ 2π − m δ_B (proof: gaps between the m boundary
  centres; every forbidden arc lies inside a gap; ordered gap points satisfy D ≥ θ_t + θ_{t+1} − δ_B).  Hypothesis
  checked in arb (margin 0.0724 at rho_test).
- **R6, boundary capacity:** exact maximum number of boundary centres with separation ≥ δ_B avoiding the
  certainly-forbidden arcs (rotation + greedy argument); prune if < m = 15 − k.
- Branching: split the widest dimension at its midpoint; boxes narrower than tol are reported as unresolved.

## 4. Arithmetic
- Float version (`bnb2.py`): margins ≥ 1e-9 everywhere (measured libm errors: cos 0.80, asin 0.89, sqrt 0.50 ulp).
- Rigorous version (`arb_bnb.py`): every prune/shrink decided in arb (96-bit) using the conservative end of each
  ball, new box ends rounded outward; capacity in exact rationals; floats only filter.

## 5. Results at rho_test
**C1 (tolerance 1e-4):**

| k | float nodes | unresolved | arb nodes | unresolved | arb pruned dist / excess / capacity / order | arb time | arb without F4: nodes / unresolved |
|---|---|---|---|---|---|---|---|
| 6 | 50,859 | 0 | 49,723 | 0 | 3,447 / 17,193 / 3,871 / 351 | 77 s | 51,949 / 0 |
| 7 | 174,191 | 0 | 171,409 | 0 | 21,869 / 49,218 / 13,084 / 1,534 | 169 s | 174,421 / 0 |
| 8 | 315,643 | 0 | 309,919 | 0 | 78,661 / 53,584 / 18,966 / 3,749 | 337 s | 318,789 / 0 |
| 9 | 498,591 | 0 | 480,865 | 0 | 194,336 / 28,970 / 11,201 / 5,926 | 433 s | 497,423 / 0 |
| 10 | 847,593 | 0 | 798,685 | 0 | 376,079 / 12,274 / 3,194 / 7,796 | 593 s | 824,945 / 0 |

**C2 (k = 5, tolerance 1e-6):** float 129,623 nodes / 503 unresolved (max distance from the pentagon 4.2e-6);
arb (rigorous) 133,019 nodes / 506 unresolved (3.46e-6).  All unresolved boxes: s ≈ 1.701302, angles ≈ 0°, 72°,
144°, 216°, 288°.  Scan: rho* − 1e-6: 0 unresolved; rho* + 1e-6: all within 8.5e-6 of the pentagon.

## 6. Validation
1. 655 explicit feasible configurations (k = 5..10, near-critical and random) followed down to box width 1e-7:
   0 failures (never pruned, never lost by shrinking).
2. k-ranges: on a grid rho ∈ {3.53, …, 3.75} × k = 5..10, survivors wherever an explicit configuration is known;
   infeasibility proven below the heuristic radius.  Side finding: a 5 + 5 + 5 configuration with k = 10 exists for
   rho ≥ 3.6987.
3. Symmetry cross-checks: k = 6 with only the rotation fixed: 8,520,805 nodes, 0 unresolved; k = 5 without symmetry
   breaking: 21,240 boxes forming exactly 24 clusters (all 4! labellings).
4. No dependence on F4 (k = 6..10 float and arb; k = 11..15 float, 1.5M–9.4M nodes).
5. Float vs arb decisions agree on 300 random k = 6 nodes.

## 7. Files
`core.py` (primitives), `bnb2.py` + `run_bnb.py` (float B&B), `arb_bnb.py` (rigorous), `validate_path.py`,
`validate_threshold2.py`, `test_*.py`, `analyze_k5.py`, `collect.py`, raw results in `results/`.

Reproduce: `python run_bnb.py 3.52135696470617 K --tol 1e-4 --workers 2`;
`python arb_bnb.py 3.52135696470617 K --workers 3` (add `--no-rm` to drop F4);
`python arb_bnb.py 3.52135696470617 5 --tol 1e-6 --out f.json` then `python analyze_k5.py f.json`.
