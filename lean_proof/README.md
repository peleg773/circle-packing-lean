# A Lean proof: optimal packings of 15 and 16 unit circles in a circle

This Lean 4 + Mathlib project proves that the best known packings of **15** and of **16** equal circles in a
circle are optimal. Optimality had previously been proven for n ≤ 14 and n = 19. The case n = 14 is due to
Ekanayake and LaFountain (2024), with an earlier proof by Fodor (2003). When this work was published (10 October 2026),
Wikipedia, NumberDB and Packomania listed n = 15 and n = 16 as conjectured, not proven. On 11 October 2026, nor
independently announced computer-assisted proofs, not formalized, for n = 15, 16, 17, 18 and 20
([blog post](https://nor-blog.pages.dev/posts/2026-10-11-circle-in-circle-packing-15-20/), [paper and code](https://nor-git.pages.dev/circle-packing/)).

**n = 15** (`CirclePacking/Final.lean`):

```lean
theorem circle_packing_15 :
    (∀ (c : Fin 15 → ℂ) (z₀ : ℂ) (R : ℝ), (∀ i, ‖c i - z₀‖ + 1 ≤ R) →
      (∀ i j, i ≠ j → 2 ≤ ‖c i - c j‖) → 1 + √(6 + 2 / √5 + 4 * √(1 + 2 / √5)) ≤ R) ∧
    ((∀ i, ‖optimal15 i‖ + 1 ≤ 1 + √(6 + 2 / √5 + 4 * √(1 + 2 / √5))) ∧
      ∀ i j, i ≠ j → 2 ≤ ‖optimal15 i - optimal15 j‖)
```

The optimal configuration is an explicit definition (`Exact15.lean`; shown without `noncomputable`, and
`optimal15` is written with `open Opt15`):

```lean
namespace Opt15
def ρ : ℝ := √(6 + 2 / √5 + 4 * √(1 + 2 / √5))
def r : ℝ := 1 / Real.sin (π / 5)
def α : ℝ := Real.arccos ((ρ ^ 2 + r ^ 2 - 4) / (2 * ρ * r))
def P (d θ : ℝ) : ℂ := ⟨d * Real.cos θ, d * Real.sin θ⟩
end Opt15

def optimal15 : Fin 15 → ℂ :=
  ![P r 0, P r (2 * π / 5), P r (4 * π / 5), P r (6 * π / 5), P r (8 * π / 5),
    P ρ α, P ρ (2 * π / 5 - α), P ρ (2 * π / 5 + α), P ρ (4 * π / 5 - α), P ρ (4 * π / 5 + α),
    P ρ (6 * π / 5 - α), P ρ (6 * π / 5 + α), P ρ (8 * π / 5 - α), P ρ (8 * π / 5 + α), P ρ (2 * π - α)]
```

So 15 non-overlapping unit disks fit inside a disk of radius `R` **if and only if**
`R ≥ 1 + √(6 + 2/√5 + 4√(1 + 2/√5)) = 4.521356965…`. In `optimal15`, five inner circles form a regular
pentagon (centres at distance `r = 1/sin(π/5)` from the centre, so neighbours touch). They are ringed by ten
circles that touch the container: centres at distance `ρ = R₁₅ − 1`, at the angles `±α` around each direction
`2πj/5`, where `α` is chosen so that each outer circle touches its inner neighbour.

**n = 16** (`CirclePacking/Final16.lean`):

```lean
theorem circle_packing_16 :
    IsGreatest {x : ℝ | Polynomial.aeval x H16 = 0} q16 ∧
    ((∀ i, ‖optimal16 i‖ + 1 ≤ R16) ∧ ∀ i j, i ≠ j → 2 ≤ ‖optimal16 i - optimal16 j‖) ∧
    ∀ (c : Fin 16 → ℂ) (z₀ : ℂ) (R : ℝ), (∀ i, ‖c i - z₀‖ + 1 ≤ R) →
      (∀ i j, i ≠ j → 2 ≤ ‖c i - c j‖) → R16 ≤ R
```

The optimal radius and an optimal configuration are explicit definitions (`Root16.lean`, `Exact16.lean`;
shown here without `noncomputable`, and `optimal16` is written with `open Opt16`):

```lean
def H16 : Polynomial ℤ := ZPoly.toPoly H16coeffs   -- 91 integer coefficients (Algebraic16Data.lean)
def q16 : ℝ := sSup {x : ℝ | Polynomial.aeval x H16 = 0}
def R16 : ℝ := 1 + √(2 / (1 - q16))

namespace Opt16
def ρ : ℝ := √(2 / (1 - q16))
def θ : ℝ := arccos q16
def B (m : ℤ) : ℂ := ⟨-ρ * cos (m * θ), -ρ * sin (m * θ)⟩
def a : ℝ := -ρ * cos (5 * θ) - √(4 - (ρ * sin (5 * θ)) ^ 2)
def d : ℝ := -ρ * cos θ + √(4 - (1 - ρ * sin θ) ^ 2)
def D : ℝ := a + ρ * cos (3 * θ) - (a - d) * (ρ * sin (3 * θ))
def b : ℝ := (a ^ 2 - ρ ^ 2 + ρ * sin (3 * θ) * (d ^ 2 + 1 - a ^ 2)) / (2 * D)
def c : ℝ := (a - d) * b + (d ^ 2 + 1 - a ^ 2) / 2
end Opt16

def optimal16 : Fin 16 → ℂ :=
  ![⟨a, 0⟩, ⟨b, c⟩, ⟨d, 1⟩, ⟨d, -1⟩, ⟨b, -c⟩,
    B (-5), B (-4), B (-3), B (-2), B (-1), B 0, B 1, B 2, B 3, B 4, B 5]
```

In words:
* `H16` is an integer polynomial of degree 90 (`H16_natDegree`). Lean does not prove that `H16` is irreducible, so
  it does not show that `q₁₆` has algebraic degree 90. Irreducibility was checked outside Lean, and nothing
  depends on it.
* `q₁₆ = 0.846993056660111759105461306…` is its largest real root. The first clause of the theorem proves that
  this `sSup` really is the largest root.
* The optimal radius is `R₁₆ = 1 + √(2/(1 − q₁₆)) = 4.615425594873193985539244…`.
* `optimal16` packs 16 unit disks in the disk of radius `R₁₆`:
  * eleven circles touch the container. Their centres `B m` lie on the circle of radius `ρ = R₁₆ − 1` at the
    angles `π + mθ` (`m = −5, …, 5`, `θ = arccos q₁₆`), so consecutive ones touch (`ρ²(1 − cos θ) = 2`);
  * five inner circles have centres `(a, 0)`, `(b, ±c)`, `(d, ±1)`.
* No smaller disk works.

Decimal brackets (`q16_bounds`, `R16_bounds`):
* `0.84699305666011175910546129 < q₁₆ < 0.84699305666011175910546132`;
* `4.615425594873193985539244 ≤ R₁₆ ≤ 4.6154255948731939855392443`.

Uniqueness of the optimum is not claimed.

`circle_packing_15_iff` and `circle_packing_16_iff` restate the optimality as an equivalence: `n` unit disks
fit in radius `R` iff `R ≥ R_n`. `circle_packing_15_euclidean` and `circle_packing_16_euclidean` state it for
points of `EuclideanSpace ℝ (Fin 2)` with `dist`. (The n = 16 variants omit the first clause, `IsGreatest …`;
it is the separate theorem `q16_isGreatest`.)

## For a skeptic: what to read, what to run, what to trust

**1. Read the statements.** They are the theorems quoted above, at the end of `CirclePacking/Final.lean` and
`CirclePacking/Final16.lean`.
* They use complex numbers or the Euclidean plane, the norm or distance, real square roots, `sin`, `cos`,
  `arccos` and `π`, and (n = 16) integer polynomials and `sSup`.
* A unit disk centred at `c i` lies in the disk of radius `R` about `z₀` exactly when `‖c i - z₀‖ + 1 ≤ R`.
* Two unit disks have disjoint interiors exactly when their centres are at least 2 apart.
* `Fin n` indexes the disks, and the distance condition forces the centres to be distinct.
* For n = 15 the statement names `optimal15` and `Opt15.ρ, r, α, P`, quoted above and printed by `Check.lean`.
* For n = 16 the statement names a few project definitions, all quoted above and printed by `Check.lean`:
  * `R16`, `q16`, `H16`, `optimal16` and the parameters `Opt16.ρ, θ, B, a, d, D, b, c`;
  * `ZPoly.toPoly`, which turns a coefficient list `[a₀, a₁, …]` into `a₀ + X·(a₁ + X·(…))`;
  * `H16coeffs`, the 91 integer coefficients of `H16`, constant term first, in `Algebraic16Data.lean`.

**2. Run the check.**

```
lake exe cache get        # download the compiled Mathlib (standard for Mathlib projects)
lake build                # check every proof and run every certificate
lake env lean Check.lean  # print the statements, their axioms, and two certificate axioms in full
```

There are no scripts, external tools or data files. Everything is in the `.lean` files, and Lean checks
all of it. The certificate computations are split into many independent files, so `lake build` uses all
available cores. With Mathlib's cache downloaded, `lake build` took about 50 minutes on a 20-thread Windows
machine. The work totals about 6 CPU-hours, almost all of it certificates.

**3. Know what is trusted.** `Check.lean` prints the axioms of each theorem:

* `propext`, `Classical.choice`, `Quot.sound`: the standard axioms of Lean and Mathlib.
* Axioms named `….native_decide.ax_1_1`, one per certificate computation file in `CirclePacking/Cert/`
  (85 files; the other 15 files only combine chunks):
  * n = 15 depends on 24 of them;
  * n = 16 depends on 62 (one, `rbAll_true`, is shared with n = 15).

  They are used only for the lower bounds. The rest of each proof uses only the kernel: that `optimal15` and
  `optimal16` are packings at the stated radius, and the algebra identifying `R16`. `Check.lean` shows, for
  example, that `optimal15_eq_Cs` (`optimal15` is the certified optimum), `q16_bounds` and `R16_bounds` depend on
  the standard axioms alone.

  Each such axiom states that one closed Boolean computation evaluates to `true`, for example

  ```
  CirclePacking.n16_k10_c3._native.native_decide.ax_1_1 :
    decide (checkChunk (P16 10) (fun _ => false) 400 16 14 3 = true) = true
  ```

  Most are one search, or one chunk of a search. A few bundle several small searches with `List.all`:
  * `n15small`, `n16small`: the cases closed at the root;
  * `rbAll`, `rb12All`: the radius bounds for 8 to 12 circles.

These computations involve only integers, rationals, lists and booleans. The search code in
`C15Compute.lean` and `C16Compute.lean` uses no floating point and no `opaque`, `extern` or
`implemented_by` declarations of its own.
* Every decision is exact: fixed-point integers (unit `2⁻⁴⁰`) in the search, exact rationals in the
  survivor tests.
* The heuristic guesses (which only steer the search) use 64-bit integers; their intermediate values stay
  below `2⁶¹`. Lean's runtime (`lean.h` in the toolchain) implements 64-bit arithmetic without undefined
  behaviour, matching the logical definitions: addition, subtraction and multiplication wrap around, and
  division by 0 and `INT64_MIN / -1` are handled explicitly.

`native_decide` runs the compiled code. This means trusting that the code generator, the C compiler bundled
with the toolchain (used because the computational core is precompiled), the runtime (`lean.h`, GMP for big
integers) and the loading of the compiled library evaluate these definitions correctly. This is the only
place where the proof relies on more than the kernel. As a cross-check, `Check.lean` lets the kernel itself
evaluate, with no compiled code, the runs that close at the root and one small search, using the same
definitions. The large searches exceed the kernel's recursion limit, so only compiled evaluation can run
them.

The certificate files import only the computational core: plain core Lean, no Mathlib. Kernel-checked
soundness theorems link them to the geometry:
* `bnb_sound`, `certified_of_checkRun` and `certified_of_chunks` in `BnB.lean`;
* the survivor analyses: `Surv.lean` (`k5_impossible`, n = 15), and `Surv16.lean` with `KFive16.lean`
  (`k5_impossible16`, n = 16).

Everything else is checked by the kernel:
* the geometric reductions, the certified cosine bounds and the soundness of every pruning rule;
* the local-uniqueness lemmas;
* the radius bounds for up to 7 circles (those for 8 to 12 circles come from certificates);
* the closed form and the explicit configuration (n = 15);
* the exact optimal configuration (n = 16): its existence, the degree-90 elimination, the root isolation
  and the explicit formulas;
* the checks that both optimal configurations are packings.

**Smaller points.**
* `lake exe cache get` downloads compiled Mathlib files. To avoid trusting them, build Mathlib from
  source (omit that step; it takes hours).
* The toolchain ships `leanchecker`. For example, `lake env leanchecker CirclePacking.Final16` re-checks
  that module's declarations with a separate kernel run (about 2–3 minutes). The certificate axioms remain
  axioms there.
* The toolchain is the release candidate `v4.35.0-rc4`, matching the Mathlib tag used.
* `L7Data.lean` (n = 15), `N16Data.lean`, `Tower16Data.lean` and the derivative lists `dH16`, `d2H16` in
  `Root16.lean` (n = 16) hold numbers computed outside Lean: approximate coordinates, multipliers,
  approximate matrix inverses, the intermediate polynomials of the elimination, and the derivatives of
  `H16`. The coefficient list `H16coeffs` (`Algebraic16Data.lean`) is part of the statement itself. Lean verifies every property the proof uses,
  in exact rational arithmetic, so nothing depends on how those numbers were found.
* If `lake build` stops with "failed to read file …olean", the machine ran out of memory, because Lake runs
  one Lean process per core. Run `lake build` again; finished files are kept, so it resumes.

## How the proofs go (module map)

Write `n` for the number of circles. The centres lie in the disk of radius `ρ` (the container radius is
`ρ + 1`) and are pairwise at least 2 apart.

**Shared machinery.**
1. **Push-out and canonical form** (`Polar.lean`, `Canon.lean`).
   * A centre with `‖c‖² > ρ² − 4` can move radially onto the circle `‖c‖ = ρ` without creating an
     overlap. Afterwards every centre is either "interior" or on the boundary.
   * The `k` interior centres are put in a canonical order by rotation, reflection and sorting by angle.
2. **Counting boundary circles** (`Greedy.lean`). Each interior centre forbids an arc of the boundary
   circle, and boundary centres keep a minimum angular gap. An exact greedy count bounds how many boundary
   centres fit.
3. **Branch and bound** (`C15Compute.lean`, `Box.lean`, `BnB.lean`).
   * The search space is the polar coordinates of the `k` interior centres.
   * A box is discarded when one of these tests excludes it: certified cosine bounds (`CosTurn.lean`), the
     pairwise-distance test, angular and radial contraction, the counting rule with radius bounds for
     fewer circles, or the capacity test.
   * `bnb_sound` proves that every admissible configuration lies in a box accepted by the survivor test.
   * `certified_of_chunks` proves that splitting a run into chunks loses nothing.
4. **Radius bounds for fewer circles** (`Radius.lean`, `Radius16.lean`, `Cert/RB*.lean`).
   * `m ≤ 7`: proved directly or with the greedy count.
   * `8 ≤ m ≤ 12`: the same branch and bound.
   * Larger `m`: by restriction.
5. **Assembly** (`Main.lean`, `Main16.lean`).
   * A packing with `ρ < ρ*` is also one at `ρ'' = max(ρ, ρ* − 10⁻⁶) < ρ*`. Every `k` except the record's
     is excluded by the search.
   * For the record's `k`, local uniqueness forces the configuration to equal `c*`, whose boundary
     centres sit at radius `ρ*`, not `ρ''`: a contradiction.

**n = 15.**
* `L7Data.lean`, `CStar.lean`: the record `c*` in exact coordinates in `ℚ(sin π/5)`.
* `L7*.lean`: exact local uniqueness, via KKT multipliers, an exact left inverse and Cauchy–Schwarz.
* `Surv.lean`: survivors of `k = 5`.
* `Exact15.lean`: the explicit configuration, `optimal15 = c*`.
* `Final.lean`: the closed form.

**n = 16.**
* `Krawczyk.lean`, `N16Data.lean`, `CStar16.lean`:
  * An exact solution `c*` of the 33 contact equations exists within `2⁻⁸⁰` of the rational point. The
    Newton map is a contraction; this uses Banach's fixed-point theorem with exact rational checks.
  * Certified polar brackets of `c*`.
* `LocalU.lean`: local uniqueness from inexact rational data, with explicit error terms. Any configuration
  satisfying the contact inequalities, and within squared distance `2.4·10⁻⁷` of `c*`, equals `c*`.
* `Angle.lean`: certified cos/sin enclosures, and angle brackets from cross products.
* `Surv16.lean`, `KFive16.lean`: survivors of `k = 5` lie in the uniqueness neighbourhood.
* `Bridge16.lean`: the structure of `c*`.
  * `c*` is mirror symmetric, because its mirror image satisfies the same constraints and is close to it, so
    local uniqueness applies.
  * Its boundary centres form a chain `c*_{p+1} = c*_p · e^{iθ}`.
  * Five contact equations remain, in the unknowns `a, b, c, d` and `q = cos θ`.
* `ZPoly.lean`, `Algebraic16Data.lean`, `Tower16*.lean`: the elimination.
  * The tower is `ℤ[q][R][t][w_a][w_d]` with `R² = 2 − 2q`, `t² = 2 + 2q`, `w_a² = 4 − 2(1+q)U₄(q)²` and
    `w_d² = 1 − 2q + 2t`. Here `R = ρ(1 − q)`, `t = ρ sin θ`, and `w_a`, `w_d` are the square roots in `a`, `d`.
  * The kernel computes the iterated norm, down to `ℤ[q]`, of the last contact equation and checks that it
    equals `2¹⁰⁰ H16(q)² (1 + 2q)²⁴ (q − 1)⁹⁶` (`decide +kernel`, about 4 minutes).
  * Hence every real solution has `H16(q) = 0`.
* `Root16.lean`: root isolation. On a rational interval of width `1.9·10⁻²⁶`, `H16` is strictly increasing
  (a derivative bound). Beyond the interval it is positive (all coefficients of the shifted polynomial are
  positive). So a root in the interval is the largest real root.
* `Bridge16.lean` (end): `H16(cos θ) = 0`, so `q16 = cos θ` and `ρ* = √(2/(1 − q16))`.
* `Exact16.lean`: `optimal16 = c*`, from the explicit formulas.
* `Final16.lean`: the theorem and the decimal brackets.

## The searches

| run | interior circles `k` | boxes (approx.) | outcome |
|---|---|---|---|
| n = 15 | 0–4, 11–15 | 1 each | closed at the root |
| n = 15 | 5 (record) | 116,000 | 464 boxes near `c*`, all pass `survOK` |
| n = 15 | 6, 7, 8, 9, 10 | 0.22M, 0.63M, 1.0M, 1.6M, 2.8M | closed |
| n = 16 | 0–4, 12–16 | 1 each | closed at the root |
| n = 16 | 5 (record, tolerance `2⁻¹⁷`) | 150,000 | 1,518 boxes near `c*`, all pass `survOK16` |
| n = 16 | 6, 7, 8, 9, 10, 11 | 0.13M, 0.58M, 1.3M, 2.1M, 3.3M, 6.0M | closed |
| radius bounds m = 8–12 | all `k ≤ m` | ≤ 3,000 each | closed |

Box counts come from development runs and may differ slightly from the certificate runs. Box widths stop
at `2⁻¹⁴`, or the stated tolerance.

Toolchain: `leanprover/lean4:v4.35.0-rc4`, Mathlib tag `v4.35.0-rc4`.
