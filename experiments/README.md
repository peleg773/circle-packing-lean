# experiments/ — code and reproduction

Python 3.10 with numpy 2.2, numba 0.68, scipy 1.15, mpmath 1.3, python-flint 0.9 (arb), matplotlib.
All rigorous steps are deterministic.  Logs of the certified runs: `out/rig_*.log`, `out/rigfast_*.log`.

## Rigorous pipeline (the proof)
| script | role | lemma |
|---|---|---|
| `local_cert.py n` | Krawczyk enclosure of the record configuration, strict inactive constraints, positive KKT multipliers, certified sigma, delta_loc (arb) -> `known_packings/local_certificate_n{n}.json` | L7 |
| `verify_L4.py rho` | disjointness of shrunk forbidden arcs (measure bound) (arb) | L4 |
| `rigmath.py` | outward-rounded interval primitives; rigorous cos / arccos series enclosures | L10 |
| `ringbb_rig.py n rho kmin kmax tol` | rigorous branch and bound over interior configurations | L1-L6, L3', L9 |
| `ringbb_rig_fast.py ...` | identical search (same tree, verified) with cached certified contraction bounds, ~2x faster | same |
| `verify_final_arb.py n rho k survivors.npy` | survivors of the record case lie in the uniqueness neighbourhood (arb + exact rationals) | L8 |
| `run_rigorous_all.sh`, `run_rigorous_n16.sh` | drivers |  |

Reproduce:
```
cd experiments
python rig_consts_gen.py            # (optional) regenerate rig_consts.json brackets with arb (already provided)
bash run_rigorous_all.sh            # n = 15, 16
```
Runtime (20 cores): n=15 ~20 min; n=16 several hours (k = 10, 11 dominate).

## Floating-point exploration (not part of the proof)
`pk_common.py`, `analyze_known.py` (reconstruct/polish Packomania packings), `search_lib.py`, `multistart.py`
(multistart local optimisation), `show_polar.py`, `ringbb.py`/`ringbb2.py` (float B&B used as fast filter and
for exploration), `final_check.py` (float version of L8), `plot_packings.py`.

## Validation of the rigorous code
`test_bmax.py`, `test_bmax2.py` (greedy vs brute force / continuous greedy), `test_rigmath.py` (interval
primitives vs mpmath), `soundness_test.py`, `soundness_random.py` (no pruning rule ever discards a strictly
feasible configuration; ~21k box tests), `positive_control.py` (B&B at a competitor's radius keeps it),
`bench_rig.py` (orig vs fast rigorous code: identical trees).


## Versions of the rigorous B&B
| module | used for | difference |
|---|---|---|
| `ringbb_rig.py` | first rigorous runs (superseded) | original |
| `ringbb_rig_fast.py` | n=16 re-runs (superseded) | caches certified contraction bounds per pair (identical trees) |
| `ringbb_final.py` | **final certified run n = 15, 16; radius bounds** | + self-proved radius table, overflow = hard failure, JSON audit log |
| `ringbb_v3.py` | exploration | + cheaper certified arccos lower bound in contraction (`rigmath_fast.py`, still rigorous) |
| `ringbb_v4.py` | exploration; `exp_lean_tree.py` (tree sizes for the Lean port) | + "deep-last" split rule (efficiency only; 80-2000x smaller trees for large k) |

## Planning tools
Tree-size estimation: `estimate_tree.py`, `estimate_tree2.py` (Knuth random probes; planning only).
