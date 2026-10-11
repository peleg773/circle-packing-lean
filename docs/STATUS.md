# STATUS

_Last update: 2026-10-11_

## Results
| n | Status |
|---|---|
| **15** | **Proved and formally verified in Lean 4 + Mathlib** (theorem `circle_packing_15`). Closed form R₁₅ = 1 + √(6 + 2/√5 + 4√(1 + 2/√5)), attained by the explicit configuration `optimal15` (an inner regular pentagon ringed by ten circles). Also proved by the Python/arb pipeline and confirmed by an independent re-implementation. |
| **16** | **Proved and formally verified in Lean 4 + Mathlib, in explicit form** (theorem `circle_packing_16`). R₁₆ = 1 + √(2/(1 − q₁₆)) = 4.6154255948731939855392441…, where q₁₆ is the largest real root of an explicit degree-90 integer polynomial H16 (irreducible by an external check, not in Lean). The explicit configuration `optimal16` (closed formulas in q₁₆) attains it. Also proved by the Python/arb pipeline. |

Axioms of each Lean theorem: `propext`, `Classical.choice`, `Quot.sound`, and one `native_decide` axiom per
branch-and-bound certificate it uses (24 for n = 15, 62 for n = 16; lower bounds only). `Check.lean` lists them.

## The Lean package (`lean_proof/`)
* One package, `CirclePacking`. The statements are in `Final.lean` (n = 15) and `Final16.lean` (n = 16);
  `Check.lean` prints the statements, the definitions they use, and their axioms.
* Self-contained: no scripts, no external tools, no data files. A skeptic runs `lake exe cache get`,
  `lake build`, then `lake env lean Check.lean`.
* All computation is integer-only; `native_decide` is used only for the branch-and-bound certificates, whose
  files import only the computational core (plain core Lean, no Mathlib).
* Kernel-checked: the geometry, pruning soundness, cos/sin enclosures, the radius bounds for m ≤ 12, exact local
  uniqueness (n = 15) and inexact local uniqueness (n = 16), existence of the exact n = 16 optimum, the survivor
  analyses, the closed form and the explicit configuration (n = 15), and for n = 16 the explicit radius and
  configuration (mirror symmetry, the degree-90 elimination, root isolation, `optimal16 = c*`).
* Development copy: `C:\Users\peleg\lean_work\circle15` (library `Circle15`); the export renames it
  `CirclePacking` and keeps only the import closure of the root module.
* Clean-build tests of the exported package: n = 15 (15.5 min); n = 15 + 16 (42.5 min); explicit n = 16
  (about 50 min, 2026-10-10); package 1.4.0 with the explicit `optimal15`: passed (44 min on a shared machine, 2026-10-11;
  `Build completed successfully (9168 jobs)`, `Check.lean` without errors).
* Referee reviews of the n = 16 package: `referee_n16_lean.md`, `referee_n16_explicit.md` (nothing fatal or
  serious; minor points fixed).
