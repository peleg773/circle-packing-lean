# Referee report: the Lean package for n = 15, 16 (2026-10-10)

An independent subagent reviewed `lean_proof/` adversarially. It read the files only and ran no build. It
focused on n = 16. Verdict: **no fatal or serious problems.**

## What the referee verified
* **The statement.** `circle_packing_16` (`Final16.lean`) has no hypotheses, since all certificates are
  discharged. Its inequalities point the right way, and the lower-bound and attainment clauses together
  pin R₁₆ to the true optimum. The decimal bracket is correctly ordered. `n16K.utq` reads `n16ut`
  (33 rationals). The referee checked numerically that `n16ut` is a packing with the claimed contact
  structure.
* **No weakening constructs.** There is no `sorry`, `admit`, `axiom`, `opaque`, `implemented_by`,
  `extern`, `unsafe`, `partial`, `csimp`, `macro`, `elab`, `#eval` or `run_cmd`, no instance tricks, and
  no Float. The only `set_option`s are `maxRecDepth`, `maxHeartbeats` and `exponentiation.threshold`.
* **`native_decide` only in certificates.** It appears only in `Cert/` (85 files). Each of those files
  imports only the computational core, and each statement has the expected form (`checkRun` or
  `checkChunk … = true`, or a `List.all` of them).
* **The axiom list.** `circle_packing_16` depends on exactly the expected 62 native axioms.
* **Coverage is complete.**
  * Every k ≤ 16 is covered, and k = 5 is handled through `survOK16` and `k5_impossible16`.
  * Every chunked run uses the same fuel, d and m as its chunk files, with all i < m present.
  * The radius bounds cover every m ≤ 15.
* **Runtime arithmetic.** Lean's runtime `Int64` operations match their logical definitions
  (`lean.h`: wrapping add/sub/mul, guarded division).

## Minor and cosmetic findings, and what was done
| # | finding | action |
|---|---|---|
| 1 | README said "the optimal configuration", which implies uniqueness | now "a configuration within 2⁻⁸⁰ of …"; descriptive facts marked informal; uniqueness explicitly not claimed |
| 2 | "integers only" was inaccurate: the survivor tests use exact rationals | README now says integers, rationals, lists and booleans, with exact decisions throughout |
| 3 | the trust base should name the code generator, bundled C compiler, runtime and GMP; a kernel cross-check would help | README spells these out; `Check.lean` now has the kernel evaluate (`decide +kernel`) the root-closed runs of n = 15 and 16 and one small search (larger searches exceed the kernel's recursion limit) |
| 4 | `Check.lean` printed axiom names only | `Check.lean` now prints two certificate axioms in full |
| 5 | the toolchain ships `leanchecker` and others | README documents `lake env leanchecker CirclePacking.Final16`, tested: passes in about 2.5 min |
| 6 | the priority claim needed a date | README: "to our knowledge … as of October 2026" |
| 7 | `_iff` and `_euclidean` omit the identification clause | stated in the README |
| 8 | "one per certificate file" | now "one per certificate computation file (85; 15 combining files)" |
| 9 | "far below 2⁶³" was loose (the maximum is about 2^60.2) | now "below 2⁶¹", citing `lean.h` |
| 10 | the radius bounds are kernel-checked only for m ≤ 7 | README corrected |
| 11 | `KFive16.lean` should be named among the soundness links | done |
| 12 | release-candidate toolchain, deprecation warnings | noted; no action |

The refreshed package is `lean_proof/` and `lean_proof_circle_packing.zip`. Only `README.md` and
`Check.lean` changed. All `.lean` proof and certificate files are byte-identical to the copy that passed the
clean build. The new `Check.lean` ran in the development project under the original library name; the
exported copy differs only by the mechanical rename.
