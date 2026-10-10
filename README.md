# Optimal packings of 15 and 16 equal circles in a circle

This repository contains computer-assisted proofs that the best known packings of **15** and **16** unit
circles in a circle are optimal. Both proofs are **formally verified in Lean 4 + Mathlib**. To our
knowledge both cases were open: as of October 2026, Packomania, NumberDB and Wikipedia listed optimality as
proven only for n ≤ 13 and n = 19.

| n | smallest container radius R for n unit circles | status |
|---|---|---|
| 15 | 1 + √(6 + 2/√5 + 4√(1 + 2/√5)) = 4.52135696470616424090… | proved, Lean-verified (`circle_packing_15`) |
| 16 | 1 + √(2/(1 − q₁₆)) = 4.61542559487319398553924…, where q₁₆ is the largest real root of an explicit integer polynomial of degree 90 | proved, Lean-verified (`circle_packing_16`) |
| 17 | 4.79203374831057917014912… (best known packing) | in progress |
| 18 | conjecturally R₁₈ = R₁₉ = 1 + √6 + √2 | in progress |

Each theorem states the optimal radius explicitly and names an explicit packing that attains it. It also
proves that no packing fits in a smaller circle.

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
| `lean_proof/` | the self-contained Lean package; the theorems are in `CirclePacking/Final.lean` and `CirclePacking/Final16.lean` |
| `RESULTS.md` | the mathematical results, and an independent proof by a Python + ball-arithmetic pipeline |
| `lemmas.md`, `proof_attempt.md` | the method: push-out lemma, exact boundary counting, branch and bound, local uniqueness |
| `STATUS.md`, `lean_plan.md` | the project's status and the formalization log, including the work on 17 circles |
| `n18_analysis.md` | the plan for 18 circles |
| `referee_n16_lean.md`, `referee_n16_explicit.md` | independent reviews of the 16-circle Lean statement |
| `experiments/` | the Python + arb pipeline (a separate, non-Lean proof for n = 14, 15, 16) and exploration code |
| `independent_check/` | a from-scratch re-implementation used to cross-check n = 15 |
| `known_packings/` | local-uniqueness certificates and the best known packings (coordinates from Packomania, E. Specht) |
| `literature.md` | references; the papers themselves are not included |

## Acknowledgments

Developed with AI assistance (Anthropic's Claude, through Claude Code). ChatGPT was also directed along the way to find an algebraic
description of the 16-circle optimum using roots of polynomials.

## License

No license has been chosen yet, so all rights are reserved by default.
