# Optimal packings of 15 and 16 equal circles in a circle

This repository contains computer-assisted proofs that the best known packings of **15** and **16** unit
circles in a circle are optimal. Both proofs are **formally verified in Lean 4 + Mathlib**.

Optimality had previously been proven for n ≤ 14 and n = 19. The case n = 14 is due to Ekanayake and
LaFountain (2024), with an earlier proof by Fodor (2003). When this work was published (10 October 2026),
Wikipedia, NumberDB and Packomania listed n = 15 and n = 16 as conjectured, not proven.

| n | smallest container radius R for n unit circles | status |
|---|---|---|
| 15 | 1 + √(6 + 2/√5 + 4√(1 + 2/√5)) = 4.52135696470616424090… | proved, Lean-verified (`circle_packing_15`) |
| 16 | 1 + √(2/(1 − q₁₆)) = 4.61542559487319398553924…, where q₁₆ is the largest real root of an explicit integer polynomial H₁₆ of degree 90 | proved, Lean-verified (`circle_packing_16`) |

Each theorem states the optimal radius explicitly, names an explicit packing that attains it (`optimal15`,
`optimal16`), and proves that no packing fits in a smaller circle.
* n = 15: a closed form in nested square roots; `optimal15` is an inner regular pentagon ringed by ten circles.
* n = 16: `q₁₆ = cos θ` is the cosine of the angle between neighbouring boundary circles, defined as the largest
  real root of H₁₆; `optimal16` is given by closed formulas in `q₁₆`. Lean proves that H₁₆ has degree 90 and
  that q₁₆ is its largest real root. That 90 is also the algebraic degree of q₁₆ (irreducibility of H₁₆) was
  checked only outside Lean; nothing depends on it.

## Check the proof yourself

```
cd lean_proof
lake exe cache get        # download the compiled Mathlib
lake build                # check every proof and run every certificate (about 50 min on 20 threads)
lake env lean Check.lean  # print the theorems, the definitions they use, and their axioms
```

`lean_proof/README.md` is written for a skeptical reader. It covers:
* what the statements say;
* what to run;
* exactly what is trusted: Lean's kernel, Mathlib, and compiled evaluation of the branch-and-bound
  certificates (`native_decide`). Everything else is kernel-checked.

## Repository layout

| path | contents |
|---|---|
| `lean_proof/` | **the proof**: a self-contained Lean package. The theorems are in `CirclePacking/Final.lean` (n = 15) and `CirclePacking/Final16.lean` (n = 16); `lean_proof/README.md` explains what to read, run and trust |
| `docs/RESULTS.md` | the mathematical results, and an independent proof of n = 15 and n = 16 by a Python + ball-arithmetic pipeline |
| `docs/STATUS.md`, `docs/lean_plan.md` | the project's status and the formalization log |
| `docs/lemmas.md`, `docs/proof_attempt.md` | the method: push-out lemma, exact boundary counting, branch and bound, local uniqueness |
| `docs/referee_n16_lean.md`, `docs/referee_n16_explicit.md` | independent reviews of the 16-circle Lean statement |
| `docs/literature.md` | references; the papers themselves are not included |
| `experiments/` | the Python + arb pipeline (the separate, non-Lean proof of n = 15 and n = 16) and exploration code |
| `independent_check/` | a from-scratch re-implementation used to cross-check n = 15 |
| `known_packings/` | local-uniqueness certificates (n = 15, 16) and the best known packings for n = 13–20 (coordinates from Packomania, E. Specht) |

## Acknowledgments

Developed with AI assistance (Anthropic's Claude, through Claude Code). ChatGPT was also directed along the way to find an algebraic
description of the 16-circle optimum using roots of polynomials.

## License

No license has been chosen yet, so all rights are reserved by default.
