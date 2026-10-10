# Lean formalization: plan and log

_Started 2026-10-10. The user wants every finished proof formalized in Lean so that a skeptic can check it
alone, quickly, without scripts._

## Status
* **n = 15: done.** `circle_packing_15` (+ `_iff`, `_euclidean`). Clean build of the exported package: passed.
* **n = 16: done (2026-10-10 13:00), explicit form 19:00.** `circle_packing_16` (+ `_iff`, `_euclidean`) now
  states the optimum explicitly: `R16 = 1 + √(2/(1 − q16))` with `q16` the largest real root of the degree-90
  `H16`, attained by the explicit `optimal16`. Axioms: 3 standard + 62 native (lower bound only).
* **Combined package** (`CirclePacking`, n = 15 + 16): the explicit-form version passed its clean test
  (about 50 min; 2026-10-10 19:45). The referee review is in `referee_n16_explicit.md`.
* **n = 17: in progress.** All modules are written. Exploration is done. The record-case survivor test is running.

## Design decisions (all cases)
* **No floating point anywhere.** The heuristics use `Int64` fixed point with unit 2⁻²⁸. Lean's runtime
  implements `Int64` without undefined behaviour (wrap-around multiplication, explicit division edge
  cases), matching the logical definitions. All decisions use exact `Int` arithmetic with unit 2⁻⁴⁰.
* **Heuristics separated from soundness.** `angStepG` and `radStepG` take the heuristic's output as an
  argument; the soundness lemmas hold for any value, and proofs never unfold heuristics.
* **Chunked certificates.** `frontier` expands the tree to depth d. `checkChunk` runs chunk i of m, with
  boxes assigned by the Knuth hash of their position. `certified_of_chunks` proves completeness.
  * Computation modules import only the computational core (core Lean, about 260 MB per process).
  * Combining modules import the soundness proofs (Mathlib, about 4 GB per process).
* **Export.** The export takes the import closure of the root module, renames `Circle15` to
  `CirclePacking`, and writes a minimal lakefile (`lean_work/tools/export_lean_proof.sh`). Every release
  is checked by a clean `lake build` of the exported folder.

## n = 16 (done): new ingredients
* `Krawczyk.lean`: an exact solution of a square contact system, from an approximate rational solution
  and an approximate inverse Jacobian. The Newton map is a contraction (exact quadratic identity
  F(u) − F(v) = J((u+v)/2)(u − v)), and Banach's theorem gives the fixed point.
* `LocalU.lean`: local uniqueness from inexact rational data. Inputs: a stress y > 0, a left inverse M
  of the gauge-fixed linearisation, and explicit residual bounds (η, E, H, K). The checks are rational
  inequalities decided by the kernel.
* `Angle.lean`, `CStar16.lean`: certified polar brackets of c* from cross products and cos/sin bounds.
* `Radius16.lean`: a radius-bound run for m = 12, with L₁₂ = 3.029299 (ρ₁₂ = 3.0296). m = 13..15
  follow by restriction.
* `Surv16.lean`, `KFive16.lean`: survivors of k = 5 (window assignment; closeness < R2 = 2.4·10⁻⁷).
* Searches: k ∈ {0..4, 12..16} close at the root. For k = 5..11 the certificates are 61 chunks. The
  record case uses tolerance 2⁻¹⁷: 1,518 survivors, all passing.
* **Explicit form** (the user's request; it follows the polynomial-root reconstruction in `ALGEBRAIC16.md`, which
  the user directed ChatGPT to find):
  * `Bridge16.lean`:
    * mirror symmetry of c*, by `local_unique_gen` applied to the mirrored configuration;
    * the chain step `c*_{p+1} = c*_p·(q + is)`, using cross-product signs;
    * the reduced system, and `H16(q) = 0`.
  * `ZPoly.lean`: integer polynomials as lists, with `eval`, `toPoly`, derivative, scaled Taylor shift
    and positivity.
  * `Tower16Defs/Data/16/Real.lean`: the tower `K4 = ℤ[q][R][t][w_a][w_d]`.
    * The kernel checks the literal intermediate values step by step, and the iterated norm equals
      `2¹⁰⁰ H16² (1 + 2q)²⁴ (q − 1)⁹⁶` (`decide +kernel`, 212 s).
    * Pitfall: a call-by-name blowup (21 GB) when a function receives unevaluated arguments and uses them
      twice. The fix was literal intermediates, with the expensive factor passed first to `ZPoly.mul`.
  * `Root16.lean`: `isGreatest_of_root`, from strict monotonicity on `[ql16, qh16]` (derivative bound)
    and a positive Taylor shift at `qh16`.
  * `Exact16.lean`: the `Opt16` parameters, `optimal16`, and `optimal16_eq_C16`.
    * The sign choices of the square roots come from the order of c*'s coordinates (rational checks).
    * `D ≠ 0` comes from interval bounds.
  * `H16_natDegree` (= 90). Irreducibility over ℚ, and hence the algebraic degree 90 of q16, is checked only
    outside Lean (degree patterns mod 3, 5, 17) and is not used.

## n = 17 (in progress)
* **Record:** 7 interior and 10 boundary circles, 25 contacts. Mirror symmetric, and the active set is
  overdetermined (35 equations, 34 + 1 − 1 unknowns).
  * The largest interior circle lies on the mirror axis, so in the canonical frame the mirror is
    (x, y) ↦ (x, −y).
  * The nearly central circle (radius 0.109) has angle 0, which gives a single canonical labelling.
* **Existence:** `Krawczyk2.lean` (`PKData`) handles points that are linear in the unknowns, with
  (x, y) = (sx·u_a, sy·u_b). The mirror-reduced system is square: 13 contact orbits + 5 boundary
  orbits = 18 unknowns. The full 35 equations follow from the mirror lemmas `X_sig` and `Y_sig`.
* **Uniqueness:** `LocalU` applied to the full overdetermined system with the symmetric stress (min 0.14 > 0);
  R2 = 8.9·10⁻⁸.
* **Radius bounds:** `Radius17.lean`. m = 13 uses a B&B run at L₁₃ = 3.23, which exceeds
  Rhi₁₇ = 3.2217, so k ≥ 13 closes at the root. That run closes for every k (at most 27K boxes).
* **Searches:** k ∈ {0..5, 13..17} close at the root. k = 6..12 cost about 10–20 CPU-hours (sampled).
  The record case uses survOK17 at tolerance 2⁻¹⁷; the test is running.
* **Files written, not yet compiled:**
  * `C17Compute.lean`, `N17Data.lean` (from `tools/gen_n17.py`, `gen_n17_lean.py`);
  * `Krawczyk2.lean`, `CStar17.lean`, `Surv17.lean`, `KSeven17.lean`, `Radius17.lean`, `Main17.lean`,
    `Final17.lean`;
  * `tools/gen_certs.py` (spec for n = 17).

* **Record-case status (2026-10-10 evening).** The native run of `survOK17b` (tolerance 2⁻¹⁸, windows
  ±2^21/S turns) failed in chunk 8: 2,335 of 92,076 survivors. The other 62 finished chunks had no
  survivors and took under 4 min each; chunk 27 is still running.
  * Cause: the box-certified arc of interior point 6 leaves a sliver of gap 8 uncovered, about 0.1–0.5·10⁻⁶
    turns.
  * Fix in progress:
    * Parameterize the window half-width: `win17h hW`, `survOK17h P hW`, `closeOK17h` (`C17Surv`),
      `surv_assign17h` (`Surv17h.lean`). `k7_impossible17` is generic in `hW`.
    * Pick `hW17r` (3.5·10⁶/S ≈ 3.2·10⁻⁶ turns). The budget is `R2 = 8.9e-8`: the windows cost about
      `10·ρ²(2π·hW)²` (21e-9 at 2^21, 58e-9 at 3.5e6), and the interior terms are below 1e-9 near c*.
  * Chunking: the near-c* cluster (92k survivors, 2 h) sits deep in one chunk. Use two-level chunks
    (`checkChunk2`, `certified_of_chunks2` in `Chunks2.lean`) so the Lean build parallelizes.
* **Explicit form for n = 17 (planned, per the user's request for explicit statements).** Given ρ, the record
  is built step by step:
  * 11 = (−√(ρ²−1), 1), from the self-mirror contact 11–12;
  * 10 = 11 rotated by φ = 2 arcsin(1/ρ);
  * 4 = (−√(ρ²−1) + √3, 0);
  * 3 = circle(4, 2) ∩ circle(10, 2), then 9 = circle(0, ρ) ∩ circle(3, 2), and 8 = 9 rotated by φ;
  * 1 on the axis at distance 2 from 3, then 2 = circle(1, 2) ∩ circle(8, 2), then 7 = circle(0, ρ) ∩ circle(2, 2);
  * 0 on the axis at distance 2 from 2.

  The last contact, |0 − 7| = 2, is one equation F(ρ) = 0 over a tower of about 8 quadratic extensions
  (the Weierstrass substitution removes √(ρ²−1)). The options are:
  * full elimination, which could give a polynomial of degree in the hundreds or thousands (kernel cost
    unclear);
  * defining ρ₁₇ as the unique zero of the explicit radical function F on an explicit interval, with a
    monotonicity proof, and `optimal17` by these radical formulas.

  Numerical check (`scratchpad/chain17.py`, 50 digits): the chain reproduces c* to 4e-50 with fixed branch
  choices. F(ρ*) = 0, F′(ρ*) ≈ 47.6, and F has exactly one sign change on [ρ* − 0.05, ρ* + 0.05].
  **Chosen definition (avoids uniqueness and elimination):** `ρ17 := sInf {ρ ∈ [a, b] | F ρ = 0}`, with rational
  a < ρ* < b.
  * F(ρ*) = 0: the chain at ρ* reproduces c*, using the contact equations, the mirror symmetry and sign
    facts, as in `Exact16`.
  * Any zero ρ′ ∈ [a, b] gives a chain configuration that is a valid packing, so the lower bound gives
    ρ′ ≥ ρ*. Validity needs interval enclosures of every chain point over [a, b]: the square-root arguments
    are > 0, the non-contact distances are ≥ 2, and the interior points are within ρ′.
  * Hence ρ17 = ρ*, and `optimal17` = chain(ρ17) attains `R17 = 1 + ρ17`.

* **Explicit form, done in the dev tree (2026-10-10, 20:30).**
  * `Chain.lean` defines the constructions `interP`, `chordStep` and `axisP`. Each comes with a lemma that
    the constructed point has the right distances, and one that a point with those distances is the
    constructed one.
  * `QIv.lean` is a rational interval library: + − × ÷ and √ at 2⁻⁶⁴, each with a soundness lemma.
  * `Exact17.lean`:
    * `F17` and the chain `ch0..ch11`;
    * `C17_k = ch_k ρ17`, via interval-checked orientation signs;
    * `F17_ρ17`;
    * `chainI`, `chainValid_rho17I` (decide +kernel, about 33 s);
    * `cfg17_packing`: every zero of `F17` in [3.79203, 3.79204] is a packing;
    * `rho17x_isLeast`.
  * `Final17.lean` states `IsLeast {zeros of F17 in [3.79203, 3.79204]} rho17x`, then that `optimal17`
    packs at `R17 = 1 + rho17x`, then the lower bound. It also has `optimal17_eq_C17`, `_iff` and
    `_euclidean`.
* **Record-case certificate layout.** `CTree` chunk trees (`C17Surv`) with `certified_of_tree` (`Chunks2`).
  * `k7tree` splits at depth 22 into 64 chunks; chunks 8 and 27 split again at +20 levels into 32 each;
    chunk 8/29 (the c* neighbourhood) splits again at +20 into 64. That makes 189 leaves.
  * `gen_certs.py` `gen_tree` writes one native leaf module per path, plus the combining module.

## n = 18 (started 2026-10-10 evening)
* **Target:** R₁₈ = R₁₉ = 1 + √6 + √2, attained by the 19-packing minus one circle (explicit, in ℚ(√2, √3)).
* **Parameters** (`explore/C18Compute.lean`):
  * `P18`: ρ = 4248186710296/2⁴⁰ = 3.86370330515638 > ρ₁₉, Rhi = 3.30578, δ = 0.0833333315 turns (< 1/12);
  * `Ltab18`: `Ltab17` for m ≤ 13, and `L₁₄ = 3.31`, certified by the radius-bound run `Prb14`.
  * `paramsOK` holds for both.
* **Lower-bound structure** (ρ'' = max(ρ, ρ₁₉ − ε) < ρ₁₉):
  * **k ≤ 6:** B ≥ 12 boundary circles need 12·φ(ρ'') ≤ 1 turn, so ρ'' ≥ ρ₁₉. This needs a separate small
    lemma, because the search alone cannot close k = 6: the 19-packing minus its centre is an 18-packing at
    ρ₁₉ whose hexagon wiggles.
  * **k ≥ 14:** the interior radius stays below 3.3058 < L₁₄ = 3.31.
  * **k = 7..13:** the search at P18.
    * Survivors are expected for k = 7, near the hexagon structures (Python: 358,814 boxes, interior
      radii ≈ 0, 2, …, 2√2), and for k = 8.
    * Matching cores, certified in Python: `hexagon_B11` (17-point core; the 11th boundary circle rattles
      in its window), `five_ring_one_s_B11`, `k8_two_s_B10`.
    * Each core needs `LocalU` data and a survivor predicate that assigns windows, including the window
      holding a single (rattling) circle.
* **Status:** `Prb14` is cheap for most k (k = 6: 47K nodes, 31 s). The sweep over k = 0..14 is running
  (`explore/logs/rb14`). Next: P18 for k = 7..13 (cost and survivors).

The optimum is not unique (`n18_analysis.md`). The plan: B&B at ρ₁₉ for k = 7..13, then three certified
rigid cores, each with a forced interior-interior contact. This needs a radius bound m = 14 above
R_I = 3.3058 (cheap, at about 3.31) and a survivor check against several structures.
