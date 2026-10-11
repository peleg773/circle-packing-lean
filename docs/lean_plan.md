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
* **n = 15, explicit form (2026-10-11).** `circle_packing_15` now names the explicit configuration `optimal15`
  (`Exact15.lean`; `optimal15_eq_Cs` is kernel-only). Package version 1.4.0; its clean build passed (44 min).
* **n = 18: done (2026-10-11).** `circle_packing_18` (+ `_iff`, `_euclidean`): `R18 = 1 + √2 + √6`, attained
  by the explicit `optimal18`. Axioms: 3 standard + 573 native (lower bound only). Package version 1.5.0.
  * Below ρ₁₉ at most 11 boundary circles (`Count18.lean`), so k ≥ 7; radius bound for 14 circles (3.31,
    `Prb14`) closes k ≥ 14 at the root.
  * Search at ρ just above ρ₁₉, tolerance 2⁻¹⁴: k = 9..13 close (chunked certificates, about 110 CPU-hours);
    k = 7, 8 leave boxes near the hexagon core (six variants, `HexCore18`) or near ten isolated structures
    (`N18CoresOK`), refined at 2⁻¹⁸ where needed (`survRef`); `Iso18`, `HexImp18` exclude them below ρ₁₉ by
    local uniqueness in exact arithmetic over ℚ(√2, √3).
  * `Opt18.lean`: `optimal18` and the exact distance check `pack18OK`.

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

