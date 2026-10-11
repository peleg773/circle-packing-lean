# RESULTS — packing 15, 16 and 18 equal circles in a circle

_Research session 2026-10-09/10.  Items marked (*) are filled from the final certified run
(`experiments/out/final/`); see section 3._

## 1. Theorems (computer-assisted)

Normalisation: n unit circles in a circle of radius R; equivalently n points in the closed unit disk with
minimum distance d = 2/(R-1).  Centres c_i with |c_i - c_j| >= 2 and |c_i| <= rho := R - 1.

**Theorem A (n = 15).**  The minimal container radius for 15 unit circles is
  R_15 = 1 + sqrt(6 + 2/sqrt5 + 4 sqrt(1 + 2/sqrt5)) = 4.52135696470616424090736400844...,
i.e. d_15 = 0.567962867736951456830766814089983272... (the root in (0.5, 0.6) of
41 d^8 - 200 d^6 + 285 d^4 - 150 d^2 + 25).  The optimal packing is unique up to isometry: an inner regular
pentagon of 5 mutually touching circles, and 10 circles touching the container, each obtained from an inner
centre by a translation of length 2 along the outer normal of an incident pentagon edge (Kravitz 1967 / Pirl 1969).

**Formal verification of Theorem A (2026-10-10).**  Theorem A (the optimal radius; uniqueness is not
formalised) is proved in Lean 4 + Mathlib: `lean_proof/`, theorem `CirclePacking.circle_packing_15`:
```lean
theorem circle_packing_15 :
    (∀ (c : Fin 15 → ℂ) (z₀ : ℂ) (R : ℝ), (∀ i, ‖c i - z₀‖ + 1 ≤ R) →
      (∀ i j, i ≠ j → 2 ≤ ‖c i - c j‖) → 1 + √(6 + 2 / √5 + 4 * √(1 + 2 / √5)) ≤ R) ∧
    ((∀ i, ‖optimal15 i‖ + 1 ≤ 1 + √(6 + 2 / √5 + 4 * √(1 + 2 / √5))) ∧
      ∀ i j, i ≠ j → 2 ≤ ‖optimal15 i - optimal15 j‖)
```
`optimal15` is the explicit configuration (`Exact15.lean`): five inner centres at distance 1/sin(π/5) in the
directions 2πj/5, and ten boundary centres at distance ρ₁₅ = R₁₅ − 1 in the directions 2πj/5 ± α, with
α = arccos((ρ² + r² − 4)/(2ρr)).  (Until package 1.3.0 the statement only asserted that an optimal packing
exists.)
`lake build` passes. There is no `sorry`, and there are no axioms beyond `propext`, `Classical.choice` and
`Quot.sound`, plus one `native_decide` axiom for each of the 24 branch-and-bound certificate chunks. Each of
those axioms states that one specific integer-arithmetic search (`checkRun …` or `checkChunk …`) returns
`true`; the build checks this by compiled evaluation (about 1.5 CPU-hours). Everything else is kernel-checked: the geometric reductions,
the soundness of the search, the trigonometric enclosures, the exact local-uniqueness lemma in ℚ(sin π/5),
the survivor analysis and the radius bounds for fewer circles. The Lean proof is a fresh implementation of
the method of section 2. It uses fixed-point integer intervals with unit 2⁻⁴⁰ instead of arb, and an exact
KKT/left-inverse uniqueness lemma instead of Krawczyk. See `lean_proof/README.md`.

**Theorem B (n = 16).**  The minimal container radius for 16 unit circles is
  R_16 = 1 + sqrt(2 / (1 - q_16)) = 4.615425594873193985539244161991965248 (+- 5e-37),
where q_16 = 0.846993056660111759105461306653800858... is the largest real root of an explicit integer
polynomial H_16 of degree 90.  q_16 = cos θ, where θ is the angle between consecutive boundary centres.
Lean proves that H_16 has degree 90 (`H16_natDegree`) and that q_16 is its largest real root.  That q_16 also has
algebraic degree 90 needs H_16 to be irreducible over ℚ, which is NOT proved in Lean.  It was checked by an
external computation: the factor-degree patterns of H_16 mod 3, 5 and 17 leave only degrees 0 and 90.  Nothing
in the proof depends on it.  Equivalently,
  d_16 = 0.5531852191443445298998869702087782279 (+- 2e-38).
The optimal packing (Goldberg 1971: 11 circles touching the container, 5 inner circles, 21 contacts, one mirror
symmetry) is unique up to isometry.

**Formal verification of Theorem B (2026-10-10; explicit form the same day).**  The optimality part of Theorem
B is proved in Lean 4 + Mathlib (uniqueness is not formalised), with the optimal radius and an optimal
configuration given explicitly.  Theorem `circle_packing_16`:
```lean
theorem circle_packing_16 :
    IsGreatest {x : ℝ | Polynomial.aeval x H16 = 0} q16 ∧
    ((∀ i, ‖optimal16 i‖ + 1 ≤ R16) ∧ ∀ i j, i ≠ j → 2 ≤ ‖optimal16 i - optimal16 j‖) ∧
    ∀ (c : Fin 16 → ℂ) (z₀ : ℂ) (R : ℝ), (∀ i, ‖c i - z₀‖ + 1 ≤ R) →
      (∀ i j, i ≠ j → 2 ≤ ‖c i - c j‖) → R16 ≤ R
```
Here `H16 = ZPoly.toPoly H16coeffs` (91 integer coefficients), `q16 = sSup {x | H16(x) = 0}`,
`R16 = 1 + √(2 / (1 - q16))`.  `optimal16` is given by closed formulas in `q16` (`Exact16.lean`):
* eleven centres `B m = -ρ e^{imθ}`, `m = -5..5`, with `ρ = √(2/(1 - q16))` and `θ = arccos q16`;
* five interior centres `(a, 0)`, `(b, ±c)`, `(d, ±1)`, with
  * `a = -ρ cos 5θ - √(4 - ρ² sin² 5θ)`,
  * `d = -ρ cos θ + √(4 - (1 - ρ sin θ)²)`,
  * `b = (a² - ρ² + ρ sin 3θ (d² + 1 - a²)) / (2D)`, where `D = a + ρ cos 3θ - (a - d) ρ sin 3θ`,
  * `c = (a - d) b + (d² + 1 - a²)/2`.

The user flagged that the first version of the theorem was existential (R₁₆ inside a decimal bracket,
attained near explicit rationals); this explicit form replaces it.  It follows an algebraic reconstruction in
terms of polynomial roots, which the user directed ChatGPT to find (`ALGEBRAIC16.md`, user-supplied).  It is now
fully kernel-checked:
* `Bridge16.lean`:
  * c* is mirror symmetric, by local uniqueness applied to its mirror image;
  * its boundary chain is `c*_{p+1} = c*_p e^{iθ}`;
  * five contacts remain.
* `Tower16*.lean`: the iterated norm of the last contact equation over `ℤ[q][R][t][w_a][w_d]` equals
  `2¹⁰⁰ H16(q)² (1 + 2q)²⁴ (q − 1)⁹⁶`.  The kernel checks this from literal intermediate polynomials
  (`decide +kernel`, about 3.5 min).
* `Root16.lean`: root isolation.  On a rational interval of width 1.9e-26, `H16` is strictly increasing,
  and the shifted polynomial has all coefficients positive.
* `Exact16.lean`: `optimal16 = c*`.

New ingredients relative to n = 15, from the first version:
* existence of c* by Banach/Krawczyk (`Krawczyk.lean`);
* inexact local uniqueness (`LocalU.lean`);
* polar brackets (`Angle.lean`, `CStar16.lean`);
* a radius bound for 12 circles (`Radius16.lean`).

Axioms: `propext`, `Classical.choice`, `Quot.sound` and 62 `native_decide` certificate axioms
(branch-and-bound chunks, lower bound only).  The algebraic identification is kernel-only (`q16_bounds` and
`R16_bounds` depend on the three standard axioms).  The Lean search needs about 13.5M boxes, against 3.1G
for the Python run of section 3.

**Theorem C (n = 18; Lean, 2026-10-11).**  The minimal container radius for 18 unit circles is
  R_18 = 1 + sqrt2 + sqrt6 = 4.86370330515627314699...,
the same as for 19 circles (Fodor 1999); equivalently d_18 = d_19 = 2 sin(pi/12) = 0.51763809020504152470...
It is attained by the 19-circle packing without one circle of its outer ring (a centre circle, six circles
around it, eleven circles touching the container), and also by several rigid configurations with seven or eight
inner circles (one or two of them at distance 2 sqrt2 from the centre), each with its mirror image.  So the
optimum is not unique.

Lean theorem `circle_packing_18` (`lean_proof/CirclePacking/Final18.lean`):
```lean
theorem circle_packing_18 :
    ((∀ i, ‖optimal18 i‖ + 1 ≤ R18) ∧ ∀ i j, i ≠ j → 2 ≤ ‖optimal18 i - optimal18 j‖) ∧
    ∀ (c : Fin 18 → ℂ) (z₀ : ℂ) (R : ℝ), (∀ i, ‖c i - z₀‖ + 1 ≤ R) →
      (∀ i j, i ≠ j → 2 ≤ ‖c i - c j‖) → R18 ≤ R
```
with `R18 = 1 + √2 + √6` and `optimal18 i` = `0`, `polar 2 ((i-1)/6)` (i = 1..6), `polar (√2 + √6) ((2(i-7)+1)/24)`
(i = 7..17), where `polar r t` is the point at distance r and angle t turns.

How the proof goes (`lean_proof/README.md`, module map):
* Below rho_19 = √2 + √6 (container radius minus 1) at most eleven centres fit on the boundary circle, since two
  of them are more than 1/12 turn apart (`card_le_eleven`).  So at least seven circles are interior.
* A radius bound for 14 circles (rho_14 > 3.31, a new branch-and-bound run) closes k >= 14 interior circles at
  the root: interior centres lie within sqrt(rho^2 - 4) < 3.306.
* The branch and bound at a rational rho just above rho_19 (tolerance 2^-14) closes k = 9..13.  For k = 7 and 8 it
  leaves 6,908 and 6,876 boxes.  All of them lie near rigid structures: the hexagon (centre and six ring circles),
  whose six boundary windows hold two circles each but one, and ten isolated structures (five and their mirror
  images).  Boxes that are too coarse are searched again at 2^-18 (`survRef`).
* For each structure, an exact core in Q(√2, √3) and inexact local-uniqueness data (`LocalU.lean`) show that a
  configuration near it equals it, and so has its boundary circles at rho_19 exactly.  This contradicts
  rho < rho_19.
* Axioms: `propext`, `Classical.choice`, `Quot.sound` and 573 `native_decide` certificate axioms (lower bound
  only).  That `optimal18` is a packing is kernel-only (exact distances in Q(√2, √3)).

**Novelty.**  Optimality was previously proven for n ≤ 14 and n = 19.  Wikipedia and NumberDB T394 record n = 14
(Ekanayake–LaFountain 2024); Packomania's bold marks still stop at 13.  As of 2026-10-09 all three list n = 15
and n = 16 as conjectured, and arXiv and citation-chain searches found no proof (literature.md).  To our knowledge
Theorems A and B were new when published here (10 October 2026), and these were the first interval-arithmetic
computer-assisted optimality proofs for equal circles in a circular container.  The proof does NOT depend on any previously published optimality result
(the radius bounds it needs for 8..13 points are re-proved by the same machinery).

## 2. Method (details: proof_attempt.md, lemmas.md)
1. **Push-out normal form (L1):** a centre with |c| > sqrt(rho^2 - 4) can be pushed radially to the boundary circle
   without creating overlaps; so WLOG every centre is on |c| = rho or in |c| <= sqrt(rho^2 - 4).
2. **Exact 1-D reduction (L2, L3):** given the "interior" centres, the boundary centres must avoid explicit
   open arcs and keep angular separation 2 arcsin(1/rho); their maximal number is computed exactly by a greedy
   algorithm on the circle (proved optimal).
3. **Rigorous branch and bound** over the interior configuration (polar boxes, symmetry reduced), for every
   possible number k of interior centres, at rho_test slightly above the conjectured rho* (covers all rho <=
   rho_test by monotonicity).  Pruning: pairwise distance, angular contraction, a measure bound (L4–L5), the
   exact boundary capacity, and radius bounds (L6).  Every pruning step is certified with outward-rounded
   interval arithmetic; cos/arccos are enclosed by explicit series with remainder bounds (no libm trust).
4. **Local uniqueness (L7):** Krawczyk-certified record configuration, certified strictly positive KKT
   multipliers and smallest singular value give an explicit radius delta_loc inside which the record
   configuration is the only one with min distance >= d*.
5. **Gluing (L8 + assembly):** all surviving boxes of the record case are certified (arb + exact rationals) to
   lie inside that neighbourhood; a scaling argument gives rho_n = rho* and uniqueness.

## 3. Certificates — final certified run
See `experiments/out/final/` (logs + one JSON audit record per (n, k)); summary by
`python experiments/summarize_final.py` (output: "ALL PROOF CONDITIONS SATISFIED: True").

| n | k | boxes | survivors | outcome |
|---|---|---|---|---|
| 15 | 5 (record) | 810,414 | 2,221 | all within 2.12e-4 (< delta_loc 1.08e-3) |
| 15 | 6, 7, 8, 9, 10 | 1.9M, 12.7M, 43.6M, 84.3M, 70.2M | 0 | closed |
| 16 | 5 (record) | 861,954 | 1,575 | all within 1.66e-4 (< delta_loc 8.71e-4) |
| 16 | 6, 7, 8, 9, 10, 11 | 3.5M, 24.6M, 135M, 534M, 1.23G, 1.19G | 0 | closed |

All runs: overflow = 0, unfinished = 0; tolerance 1e-5 (record case) or 0.02 (others).  (That run also re-proved the
known case n = 14 as a calibration, hence the line "n=14 done" in `TIMES.txt`; its outputs are no longer kept.)
(The Lean searches of section 1 prune much harder, by iterated contraction: about 13.5M boxes in total for
n = 16, against 3.1G here.)

## 4. Reproduction
```
cd experiments
bash run_final.sh             # certificates, L4, radius bounds, B&B for n = 15, 16, survivor checks
python summarize_final.py     # checks every completeness condition (all k present, overflow = 0, ...)
```
Software: Python 3.10.9, numba 0.68.0, numpy 2.2.6, python-flint 0.9.0 (arb), mpmath 1.3.0, scipy 1.15.3.
Source hashes: `experiments/out/final/SOURCE_HASHES_at_launch.txt`.  Runtime on 20 cores: about 5 h (n = 15: 17 min, n = 16: 4 h 41 min; `out/final/TIMES.txt`).
Set OPENBLAS_NUM_THREADS=1 (done in the script), otherwise 20 worker processes exhaust Windows commit memory.

## 5. Validation
* Independent adversarial review of all lemmas and rigorous code: no fatal error; ~500k adversarial unit tests
  of the primitives, greedy bound, contraction, end-to-end mini-runs (experiments/out/SKEPTIC_REPORT.md).
* Randomised soundness tests: ~21,000 box tests on ~5,200 strictly feasible configurations: no false prune.
* Positive controls: B&B at the container radius of the two best n = 15 competitors (0.17 %, 0.25 % worse)
  keeps them.
* Exact closed form for n = 15 checked to lie in the Krawczyk uniqueness box (deviation 4.6e-46 vs 1e-38).
* Independent re-implementation of the n = 15 search by a separate agent (written from scratch, without reading
  `experiments/`): C1 (k = 6..10 closed) and C2 (every admissible k = 5 configuration is within 3.46e-6 of the
  pentagon configuration) CONFIRMED, in a float B&B with margins and in a fully rigorous arb B&B
  (`independent_check/REPORT.md`).

## 6. Weakest points (for a skeptical expert, in order)
For n = 15 the points below concern only the Python pipeline. The Lean proof (section 1) leaves two trusted
components: the Lean kernel with Mathlib, and compiled evaluation of the 8 search certificates
(`native_decide`).
1. Correctness of the rigorous B&B code (`ringbb_final.py`, `rigmath.py`); in particular the soundness of the
   pruning rules as implemented (reviewed and stress-tested, not formally verified).  Floating-point filters
   only decide whether a rigorous check is attempted; they cannot cause unsound pruning.
2. Reliance on IEEE-754 correct rounding of + - * / sqrt in numba/LLVM-compiled code (nextafter widening is
   robust to FMA contraction; no fast-math).
3. The radius bounds rho_m > L_m (m = 8..13) are produced by the same code (not an independent check).
4. The final gluing step (survivor boxes -> full configurations -> distance to c*) — exact-rational decisions,
   but intricate (assignment enumeration of boundary points).
5. Reproducibility so far only on one machine (Windows 11, x86-64).
