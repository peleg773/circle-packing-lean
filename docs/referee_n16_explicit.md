# Referee report: the explicit n = 16 statement (2026-10-10, 19:15)

**Reviewed.** The new `circle_packing_16`:
```lean
theorem circle_packing_16 :
    IsGreatest {x : ℝ | Polynomial.aeval x H16 = 0} q16 ∧
    ((∀ i, ‖optimal16 i‖ + 1 ≤ R16) ∧ ∀ i j, i ≠ j → 2 ≤ ‖optimal16 i - optimal16 j‖) ∧
    ∀ (c : Fin 16 → ℂ) (z₀ : ℂ) (R : ℝ), (∀ i, ‖c i - z₀‖ + 1 ≤ R) →
      (∀ i j, i ≠ j → 2 ≤ ‖c i - c j‖) → R16 ≤ R
```
It names these definitions:
* `H16 = ZPoly.toPoly H16coeffs` (degree 90);
* `q16 = sSup {roots}`;
* `R16 = 1 + √(2/(1 − q16))`;
* `optimal16`, built from the `Opt16` closed formulas.

The reviewer was an independent subagent that modified no files.

**Verdict: no critical problems.** The statement faithfully and non-vacuously formalizes "R16 is the minimum container
radius for 16 non-overlapping unit disks, attained by `optimal16`".

**What was checked**
* **Conventions.** Containment is `‖c − z₀‖ + 1 ≤ R`, and disjoint interiors is a centre distance ≥ 2. Quantifiers and
  inequality directions are right, and the `_iff` and `_euclidean` variants are correct.
* **No junk values:**
  * `sSup` is pinned down by the `IsGreatest` clause;
  * `0 < 1 − q16` and `−1 ≤ q16 ≤ 1` hold (re-proved in a scratch file);
  * the arguments of both square roots are proved to be squares (2.553 and 3.150);
  * `D < 0` is proved (`D16_neg`; numerically D ≈ −9.723).
* **The formulas match `ALGEBRAIC16.md` §2 term by term** (the note the user had ChatGPT compute). Both square-root signs are correct; the other
  choices put the centres outside the container.
* **Numerics** (mpmath at 120 digits, python-flint):
  * the coefficients match, and H16 is primitive and irreducible with 24 real roots;
  * the largest root is q = 0.846993056660111759105461306653800858…, and both decimal brackets hold;
  * there are exactly 21 contacts, with |d − 2| ≤ 6e−114, and the nearest non-contact pair is 2.039 apart;
  * the configuration agrees with the rational record `n16ut` to 3.6e−34.
* **The elimination identity, independently:** ∏ over the 16 conjugates of `F16real` equals
  2¹⁰⁰·H16²·(1+2q)²⁴·(q−1)⁹⁶ to 7e−133 at four test points.
* **Proof chain:**
  * The new files contain no `sorry`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe` or `opaque`.
  * These depend only on the three standard axioms: `q16_isGreatest`, `optimal16_eq_C16`, `cstar16_packing`, `R16_eq`,
    `H16_natDegree`, `H16_qg`, `u16_mirror` and `H16_eval_eq_zero`.
  * The 62 `native_decide` axioms enter only through the lower bound.

**Minor and cosmetic points, all addressed**
1. `Check.lean` now prints the axioms of `q16_isGreatest`, `optimal16_eq_C16`, `cstar16_packing`, `R16_eq` and
   `H16_natDegree`, all standard-only.
2. `Check.lean` now shows `ZPoly.toPoly.eq_1/eq_2` and `H16_coeff`, and prints the full coefficient list (the `#print`
   of the list was unreadable).
3. The README's definitions block says it omits `noncomputable` and uses `open Opt16`.
4. The README lists the derivative lists `dH16` and `d2H16` among the numbers computed outside Lean, and notes that
   `H16coeffs` is part of the statement.
5. The README notes that the `_iff` and `_euclidean` variants omit the `IsGreatest` clause; it is `q16_isGreatest`.
6. The isolating interval's width is now stated as 1.9·10⁻²⁶.
7. `ALGEBRAIC16.md` (the user-supplied note) is out of date: it says the elimination is not formalized. That is now superseded.
   The note is the user's file and was left unchanged.

**Clean test.** The exported package (`lean_proof/`, `lean_proof_circle_packing.zip`) built from scratch:
`Build completed successfully (9167 jobs)`, about 50 min. The run shared the machine with other jobs, three modules
hit the out-of-memory symptom, and a resume finished them. `Check.lean` output is as expected.
