# n = 18: the "one missing point" analysed in the push-out framework

Conjecture: d_18 = d_19 = 2 sin(pi/12), i.e. rho_18 = rho_19 = 1/sin(pi/12) = sqrt6 + sqrt2 (unit circles).

## 1. Reformulation (exact)
By the push-out lemma (L1) and the exact boundary reduction (L2, L3), for every rho:
* "n points fit in radius rho"  <=>  there are k interior points I (pairwise >= 2, radii <= R_I(rho)) with
  Bmax_rho(I) >= n - k.
* For rho < rho_19 one has 12 delta_B(rho) > 2 pi, so B <= 11 and k >= 7.
Hence (with R_I(rho_19) = 3.3058 < rho_14 = 3.3284, so k <= 13):

| statement | equivalent inequality for all rho < rho_19 and all admissible I (|I| = k) |
|---|---|
| Fodor's theorem (n = 19) | Bmax_rho(I) <= 18 - k  for k = 8..13 (k = 7 forces B = 12: impossible) |
| conjecture (n = 18) | Bmax_rho(I) <= 17 - k  for k = 7..13 |

So the 18-point conjecture asks for exactly one less boundary capacity, for every interior configuration.

## 2. Why counting arguments cannot see the missing point
Measure bound (L5): B delta_B + sum e(s_j) <= 2 pi.  At rho slightly below rho_19 (computed in
`experiments`, see lemmas.md O7):
* centre + 5 ring points (radius 2) + one point at radius 2 sqrt2, with 11 boundary points: slack -> 0
  (excluded by the measure bound for every rho < rho_19 at these radii — tight, like n = 15's optimum);
* centre + 5 ring + two 2 sqrt2-points, 10 boundary points: slack -> 0 (same);
* **centre + full hexagon (radius 2), 11 boundary points: slack 30 deg.**  This is "the 19-packing minus one
  outer point".  Its exclusion below rho_19 cannot come from any counting/measure argument; it comes from the
  discrete window structure: the six ring points cut the boundary circle into six windows of width
  60 deg - 2 theta(2) = 30 deg - O(rho_19 - rho); a window holds two boundary points only if its width is
  >= delta_B = 30 deg + O(rho_19 - rho), i.e. only at rho = rho_19 exactly.  For the exact hexagon,
  Bmax = 12 at rho_19 but Bmax = 6 for every rho < rho_19 (computed).

## 3. First-order rigidity of the critical family (lemmas.md O8, O9)
* No perturbation of the 7-point hexagonal cluster (respecting its contacts to first order) widens the five
  2-point windows simultaneously (LP value exactly 0).
* The 17-point CORE (centre + hexagon + the 10 boundary points filling 5 windows; i.e. the 19-packing minus
  both outer points of one window) is a strict local maximum of the minimum distance at 2 sin(pi/12):
  rigorously certified (`core_cert.py n18_hexagon_core17`): exact lattice coordinates, 31 contacts + 10
  boundary constraints, certified strictly positive multipliers (>= 0.0191), certified smallest singular value
  0.355, delta_loc >= 6.82e-4.  (Calibration: the full 19-packing certifies with delta_loc >= 9.25e-4.)
  Consequently every 18-point configuration within 6.8e-4 (point normalisation) of "19-packing minus one outer
  point" has minimum distance <= 2 sin(pi/12), whatever the sliding 18th point does.

## 4. Proposed complete route (same machinery as n = 15, 16)
1. B&B (interior configurations, k = 6..13) at rho_test slightly above rho_19.  All survivors should lie near
   finitely many interior structures (centre/ring/2sqrt2-points of the 19-lattice); rattler families of the
   original problem become boundary points after push-out, so their interior configurations are isolated.
2. For each surviving structure, an L7-type certificate for a rigid core (as in section 3), with exact
   lattice coordinates.
3. Final check: survivors' cores lie within the certified neighbourhoods; scaling/strictness argument as for
   n = 15, 16 (every structure has interior-interior contacts).
Main unknown: the B&B cost for k = 11..13 with R_I = 3.306 (larger than for n = 16).  Status: exploration
runs (`run_n18_explore.sh`) queued.

## 5. Proof plan in detail (implemented: core_cert.py, n18_structures.py, verify_cores_n18.py, ringbb_v4.py)
Suppose rho(Y) < rho_19.  Scale by lambda = rho_19/rho(Y) > 1 (distances >= 2 lambda > 2) and push out at rho_19
-> Yhat (boundary radius rho_19; interior radius <= R_I = 3.3058; interior-interior distances >= 2 lambda > 2).
* **|B| <= 11.**  The centres that end on the boundary have radii in (R_I, rho_19] in the scaled configuration;
  on [R_I, rho_19]^2 the minimal angle for distance >= 2 is 30 deg, attained only at (rho_19, rho_19) (max of
  f(r,s) = (r^2+s^2-4)/(2rs) over the square is at a corner: f(rho,rho) = cos 30 > f(R_I,rho) = R_I/rho), and for
  distance > 2 it is strictly larger; so 12 of them would need more than 360 deg.  Hence k >= 7.
* **k <= 13** by the self-proved bound rho_14 > L_14 = 3.32842523 > R_I.
* **B&B** (ringbb_v4, rigorous) at rho_test = rho_19 (+4e-15) for k = 7..13: every canonical interior
  configuration of Yhat lies in a surviving box.
* **Cores** (core_cert.py, exact lattice coordinates, certified): hexagon_B11 (17-point core,
  delta_loc >= 6.82e-4), five_ring_one_s_B11 (whole 18-point configuration is an ISOLATED strict local maximum,
  delta_loc >= 7.73e-4), k8_two_s_B10 (isolated, delta_loc >= 8.07e-4).  Each core contains a centre-ring
  contact (interior-interior distance exactly 2).
* **Survivor certification** (verify_cores_n18.py, exact rationals): for every surviving box and every
  assignment of the boundary points to allowed intervals, some rotation/reflection/relabelling of some
  certified core lies within rho_19 * delta_loc(core).
* Then L7 for that core forces an interior-interior contact in Yhat: contradiction.  Hence rho_18 = rho_19.
Status: k = 7, 8 searches running; k = 9..13 queued after n = 16.
