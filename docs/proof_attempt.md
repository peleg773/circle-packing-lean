# Proof: optimality of the best-known packings of 15 and 16 equal circles in a circle

**Status (2026-10-10):** complete computer-assisted proof, conditional only on the correctness of the
certified computations listed in section 8 (final certified run: `experiments/out/final/`).  Independent
adversarial review: no fatal error found in the mathematics or the rigorous code (report:
`experiments/out/SKEPTIC_REPORT.md`; all its minor points addressed, see section 9).
Literature dependence: NONE beyond elementary facts (the radius bounds rho_m, m <= 13, needed by the search are
re-proved by the same machinery; section 4).

## 0. Statements
Unit-circle normalisation: centres c_1..c_n, |c_i - c_j| >= 2, |c_i| <= rho; rho_n = min rho; R_n = rho_n + 1;
d_n = 2/rho_n (max-min distance of n points in the unit disk).

**Theorem 16.** rho_16 = rho*_16 where rho*_16 = 3.615425594873193985539244161991965248... is defined by the
contact structure of the packing c*_16 below (rigorous enclosure radius 5e-37);
d_16 = 0.55318521914434452989988697020877822(79 +- 1e-38), R_16 = 4.615425594873193985539...
The optimal packing (Goldberg 1971) is unique up to isometry: 11 circles touch the container, 5 inner circles,
21 contacts, one mirror symmetry.

**Theorem 15.** rho_15 = sqrt(6 + 2/sqrt5 + 4 sqrt(1 + 2/sqrt5)) = 3.52135696470616424090736400844...,
R_15 = 1 + sqrt(6 + 2/sqrt5 + 4 sqrt(1 + 2/sqrt5)), d_15 = 0.56796286773695145683... (the root in (0.5,0.6)
of 41d^8 - 200d^6 + 285d^4 - 150d^2 + 25).  The optimal packing (Pirl/Kravitz: an inner regular pentagon of
side 2; each outer circle = an inner vertex + 2 * (outer unit normal of an incident pentagon edge)) is unique
up to isometry.

## 1. Push-out normal form (L1)
Any centre with |c| > R_I := sqrt(rho^2 - 4) can be pushed radially onto |c| = rho keeping all distances >= 2.
After pushing all such centres: n-k "boundary" centres on |c| = rho, k "interior" centres with |c| <= R_I.

## 2. Exact reduction (L2, L3)
Interior q = s e^{i psi} forbids the open boundary arc of half-width theta(s) around psi (none if s <= rho-2);
boundary centres need angular separation delta_B = 2 asin(1/rho).  The configuration exists iff Bmax(I) >= n-k,
with Bmax computed exactly by the greedy of L3.  All constraints are monotone in rho, so a search at
rho_test >= rho* covers all rho <= rho*.  Ranges of k: n-k <= floor(2 pi / delta_B) gives k >= 5 (n = 15, 16);
interior points lie in the disk of radius R_I, which cannot hold
11 points (n=15: R_I = 2.8983 < L_11 = 2.92380) or 12 points (n=16: R_I = 3.0119 < L_12 = 3.02960),
with L_m the proven bounds of section 4.

## 3. Rigorous branch and bound (ringbb_final.py)
For every k in range, the k interior points in canonical form (s_0 >= ... >= s_{k-1}, psi_0 = 0, psi_1 in [0,pi])
are enclosed in polar boxes.  A box (or part of a box) is discarded only if certified with outward-rounded
interval arithmetic (L10; no libm trust):
 * P4: ordering and s_j >= L_{k-j} (L6 with the self-proved table);
 * contraction (L9): angles psi_b within a certified lower bound of the minimal interior-interior angle
   theta_II of every psi_a in a's interval are removed;
 * P1: some pair of boxes has certified maximal distance < 2 (exact max over polar boxes by convexity);
 * P2a: measure bound (L5, using L4 certified at rho_test) violated;
 * P2: certified upper bound on Bmax (L3') is < n-k.
Every run must end with overflow = 0 and unfinished = 0 (enforced and logged).

## 4. Literature-free radius bounds (prove_radius_bounds.py)
Elementary: rho_m >= 1/sin(pi/m) for m <= 6 (for rho < 2 the push-out moves every centre onto the circle), and
rho_7 >= rho_6 = 2.  Then, for m = 8..13 in order, the same B&B at rho_test = L_m := rho_m^approx (1 - 1e-6)
(using the table proved so far) finds no surviving box for any k, hence rho_m > L_m.

## 5. Local uniqueness (L7)
Krawczyk-certified record configuration, strictly positive KKT multipliers, certified smallest singular value
=> explicit delta_loc: no other configuration with min distance >= d* within (rotation-aligned) Euclidean
distance delta_loc.  delta_loc >= 3.079e-4 (n=15), 2.409e-4 (n=16).

## 6. Survivors in the neighbourhood (L8, verify_final_arb2.py)
For the record case k (k = 5 for n = 15 and n = 16) all surviving boxes (tolerance 1e-5) are turned into
enclosures of full configurations (boundary angles by exact interval propagation over all assignments of
boundary points to allowed intervals) and certified to lie within rho* delta_loc of c* (exact-rational decisions).

## 7. Assembly
Let Y have rho(Y) < rho*.  Scale by lambda = rho*/rho(Y) > 1 (all distances >= 2 lambda > 2) and push out at rho*
(section 1) to get Yhat (interior centres unchanged, so interior-interior distances >= 2 lambda > 2).  By
sections 2-4, Yhat has k equal to the record value and its canonical interior lies in a survivor box; by
section 6, |Yhat - c*| < rho* delta_loc after rotation/reflection/relabelling; by section 5 applied to Yhat/rho*
(unit disk, min distance >= d*), Yhat is congruent to c*.  But c* has interior-interior contacts (distance
exactly 2): contradiction.  Hence rho_n = rho* (attained by c*).
Uniqueness: let rho(Y) = rho*; then Yhat is congruent to c*.  Call a centre MOVED if the push-out actually changed
it (|y| < rho* before).  If a moved centre b had a contact (in Yhat) with an unmoved centre c, the pull-in
corollary of L1 gives |y_b - y_c| < 2 in Y: impossible.  So the set of moved centres is closed under contacts
of c*; the contact graph of c* is connected and contains interior centres, which never move; hence nothing
moved and Y = Yhat is congruent to c*.

## 8. Certificates (final run, out/final/)
(filled in RESULTS.md section 3 after the run)

## 9. Responses to the adversarial review
F1 (incomplete rigorous runs) -> complete final run for all k (out/final/*.log, JSON per (n,k)).
S1 (auditability) -> JSON record per run (parameters, table, counts, overflow, unfinished, timing).
M1/M2 -> verifier rewritten: no wrap-around (point 0's gap arc certified), full segment when no other arcs,
exact-rational decisions (verify_final_arb2.py).  M3 -> theta bounded via the R_I ball.  M4 -> L3 proof
replaced by the reviewer's rotation argument.  M5 -> wording fixed ("moved"), contraction described correctly.
M6 -> the reduction rule P3 is not used anywhere in the rigorous code.  M7 -> overflow is a hard failure.
M8 -> rigorous assertion y_m != 0.  M9 -> fresh numba cache directory for the final run.  M10 -> soundness
tests also check that contraction keeps feasible points.  M11 -> literature-free radius bounds (section 4).
