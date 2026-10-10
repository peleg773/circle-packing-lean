# STATUS

_Last update: 2026-10-10 19:55_

## Goal
Prove that the best-known packings of n equal circles in a circle are optimal (computer-assisted proofs),
for the smallest open cases, and formalize every finished proof in Lean so that a skeptic can check it
alone (no scripts).

## Where things stand
| n | Status |
|---|---|
| **15** | **Proved and formally verified in Lean 4 + Mathlib** (theorem `circle_packing_15`). Closed form R = 1 + √(6 + 2/√5 + 4√(1 + 2/√5)). Axioms: the three standard ones plus 24 `native_decide` certificate axioms. Also proved by the Python/arb pipeline and confirmed by an independent re-implementation. |
| **16** | **Proved and formally verified in Lean 4 + Mathlib, in explicit form** (theorem `circle_packing_16`, explicit since 2026-10-10 19:00). R₁₆ = 1 + √(2/(1 − q₁₆)) = 4.6154255948731939855392441…, where q₁₆ is the largest real root of an explicit degree-90 integer polynomial H16 (irreducible over ℚ). An explicit configuration `optimal16` (closed formulas in q₁₆: √, arccos, cos, sin) attains it. Axioms: the three standard ones plus 62 `native_decide` certificate axioms (lower bound only). Also proved by the Python/arb pipeline. |
| 17 | **In progress, mostly done (Lean directly).** The Lean proof compiles with only the standard axioms, given the branch-and-bound certificates as hypotheses. All certificates except the record case are built: k = 0..6 and 8..17, plus the radius bound for 13 circles (105 modules, 2.4 h). The record case k = 7 is heavy. Its interior circle near the centre blocks no boundary arc, so the survivor predicate uses six arcs (`C17Surv.lean`, tolerance 2⁻¹⁸). Near the optimum it passes, and the full native run is in progress (64 chunks). A competing local optimum is only 7.6·10⁻⁵ worse and close in configuration space. |
| 14 | Known theorem (Fodor 2003; Ekanayake–LaFountain 2024). Re-proved with the Python code as calibration. |
| 18 | Harder: the optimum is not unique (`n18_analysis.md`). Global Python search partly done (k = 7). |

## The Lean package (`lean_proof/`, being refreshed)
* One package, `CirclePacking`, proves both n = 15 and n = 16. The statements are in `Final.lean` and
  `Final16.lean`, and `Check.lean` prints the statements and their axioms.
* Self-contained: no scripts, no external tools, no data files. A skeptic runs `lake exe cache get`,
  `lake build`, then `lake env lean Check.lean`.
* All computation is integer-only. There is no floating point anywhere, and the 64-bit heuristics follow
  Lean's runtime semantics with no undefined behaviour. `native_decide` is used only for the
  branch-and-bound certificates. Their files import only the computational core, not Mathlib.
* Kernel-checked:
  * the geometry;
  * pruning soundness;
  * cos/sin enclosures;
  * the radius bounds for m ≤ 12;
  * exact local uniqueness (n = 15) and inexact local uniqueness (n = 16, `LocalU.lean`);
  * existence of the exact n = 16 optimum (Banach/Krawczyk, `Krawczyk.lean`);
  * the survivor analyses;
  * the closed form (n = 15);
  * for n = 16: the explicit radius and configuration, i.e. the mirror symmetry of c*, the degree-90
    elimination (`Tower16`), the root isolation (`Root16`) and `optimal16 = c*` (`Exact16`).
* Development project: `C:\Users\peleg\lean_work\circle15`, a git repository; `.lake` takes 7 GB. The
  export renames the library `Circle15` to `CirclePacking` and keeps only the import closure
  (`lean_work/tools/export_lean_proof.sh`).
* Clean-build tests:
  * n = 15 package: passed (15.5 min).
  * Combined n = 15 + 16 package: passed (42.5 min), with all axioms as expected.
  * Explicit-form n = 15 + 16 package: passed (about 50 min).
* A referee subagent reviewed the n = 16 package and found nothing fatal or serious; the minor points are
  fixed (`referee_n16_lean.md`).
* The user flagged that the n = 16 statement was existential, with no explicit radius or construction. It
  now names `R16`, `q16`, `H16` and `optimal16` (following ChatGPT's `ALGEBRAIC16.md`).
  * Clean test of the new package: passed (about 50 min; `Build completed successfully (9167 jobs)`).
  * Referee review: no critical problems; the minor points are fixed (`referee_n16_explicit.md`).
  * `lean_proof/`, the zip and the artifact page are refreshed.

## Next actions
1. n = 17: the record-case native run found 2,335 failing survivors in chunk 8 (of 92,076). They sit
   near c*, but the arcs of interior point 6 leave a sliver of gap 8 uncovered.
   * Fix found: windows of half-width 3.5·10⁶/S. Near c*, every one of 148,546 survivors passes, against
     610 failures with the old width; the error budget used is 59.5e-9 of 89e-9.
   * Lean side: written and generic in the half-width (`survOK17h`, `Surv17h`, `KSeven17`, `Chunks2`).
   * Next: choose the chunking (chunks 8 and 27 are heavy), rerun the record case natively, build the
     Lean certificates and `Final17`, and add the explicit form (chain construction, see `lean_plan.md`).
2. n = 18: decide the approach (non-unique optimum).
