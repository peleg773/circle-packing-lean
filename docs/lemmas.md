# Lemmas

Status labels: `PROVED` (complete proof written here), `PROVED (computer)` (proof relies on a rigorous
computation whose code is in `experiments/`), `NUMERICALLY TESTED`, `CONJECTURED`, `DISPROVED`.

**Normalisation.** Unless said otherwise we use *unit circles*: centres c_1..c_n in R^2 with |c_i - c_j| >= 2,
all centres in the closed disk of radius rho (container radius R = rho + 1).  rho_n := minimal such rho.
Point normalisation: p_i = c_i / rho in the unit disk with min distance d = 2/rho.

Notation (rho > 2 fixed):
  theta(s) = theta_rho(s) := arccos( (s^2 + rho^2 - 4) / (2 s rho) )  for rho-2 < s <= R_I;  theta(s) := 0 if s <= rho-2
  delta_B := 2 arcsin(1/rho)        R_I := sqrt(rho^2 - 4)        E := sqrt(rho^2 - 1) - sqrt(3)
  theta_II(s,t) := arccos( clip((s^2 + t^2 - 4)/(2 s t), -1, 1) )
  e(s) := max(0, 2 theta(s) - delta_B)     ("excess"; e(s) > 0  <=>  s > E: "gap point", else "pocket point")

---------------------------------------------------------------------------------------------------
## L1 Push-out lemma — PROVED
Let |c_i - c_j| >= 2 (i != j) and |c_i| <= rho.  If |c_p| > R_I, replacing c_p by rho c_p/|c_p| keeps all
distances >= 2.  Iterating: WLOG every centre satisfies |c| = rho ("boundary point") or |c| <= R_I
("interior point"); interior points are unchanged.
*Proof.* u = c_p/|c_p|, f(t) = |t u - c_j|^2 on [|c_p|, rho], s = |c_j| <= rho.  If f(t0) = 4 with t0 > R_I then
2 s cos = (t0^2 + s^2 - 4)/t0, hence f'(t0) = (t0^2 - s^2 + 4)/t0 > 0 (t0^2 > rho^2 - 4 >= s^2 - 4).  If
{t : f(t) < 4} were non-empty, its infimum t1 would satisfy f(t1) = 4 and f'(t1) <= 0: contradiction.
Other centres keep their radii, so the argument applies to each pushed point in turn (other points may
themselves have been pushed earlier; only |c_j| <= rho is used).  []
*Corollary (pull-in).* If |c_b| = rho, |c_b - c_j| = 2 and c_j is fixed, then moving c_b radially inward to any
radius in (R_I, rho) makes |c_b - c_j| < 2 (same crossing argument).  Used for uniqueness.

## L2 Exact boundary feasibility — PROVED
|rho e^{ia} - s e^{i psi}| >= 2  iff  |a - psi|_circ >= theta(s);   |rho e^{ia} - rho e^{ia'}| >= 2 iff
|a - a'|_circ >= delta_B.  theta is strictly increasing on (rho-2, R_I]; theta_rho(s) and delta_B are decreasing
in rho, R_I increasing in rho.
*Proof.* Law of cosines; d/ds[(s^2+rho^2-4)/(2 s rho)] = (s^2 - rho^2 + 4)/(2 s^2 rho) < 0 for s < R_I;
d/drho[...] = (rho^2 - s^2 + 4)/(2 s rho^2) > 0.  []
**Consequence (exact reduction).** After L1, a configuration with k interior points I exists iff Bmax(I) >= n-k,
where Bmax(I) := max number of points on the circle with pairwise circular distance >= delta_B avoiding the
open arcs (psi_q - theta(s_q), psi_q + theta(s_q)), q in I.  All constraints are weaker for larger rho, so a
search with parameter rho_test covers every configuration with container radius rho <= rho_test.

## L3 Greedy computes Bmax exactly — PROVED
Let A be a finite union of closed arcs, A != circle, delta > 0.  The maximum number N of points of A with
pairwise circular distance >= delta equals max over left endpoints a of arcs of A of G(a), where G(a) places
x_1 = a, then repeatedly the smallest point of A that is >= x_prev + delta, stopping when it exceeds a+2pi-delta.
*Proof.* (i) Normalisation (simplification suggested by the independent reviewer): take an optimal placement
x_1, ..., x_N, let L_i be the left endpoint of the arc of A containing x_i and tau = min_i (x_i - L_i) >= 0.
Rotating ALL points clockwise by tau keeps every point in its arc (x_i - tau >= L_i) and all gaps unchanged,
and the minimising point lands on a left endpoint.  (ii) Fixed first point: if a = y_1 < ... < y_M <=
a + 2pi - delta is feasible, the greedy positions satisfy g_j <= y_j by induction (y_{j+1} >= y_j + delta >=
g_j + delta and y_{j+1} in A), so G(a) >= M.  Hence max_a G(a) >= N, and G(a) <= N trivially.  []

## L3' Rigorous upper bound by the floating-point greedy — PROVED (code: `bmax_rig`, ringbb_rig*.py)
Inputs: shrunk forbidden arcs (lo_j, hi_j) contained in the true certainly-forbidden arcs; step
dlt = dn(delta_lo - 2 EPS) <= delta_B - 2 EPS; lifted copies (shifted by sh * 2pi with sh in -2..3, endpoints
rounded INWARD using rigorous brackets of 2pi).  Starts: right endpoints hi_j not strictly inside a lifted arc.
From start a: z = dn(x + dlt) (rounded down), then jump to the right endpoint of any lifted arc strictly
containing z (repeat), place if z <= up(up(a + 2pi_hi) - dlt).
Claim: result >= true Bmax.  *Proof.*  Let A' be the complement of the shrunk arcs (A' contains the true allowed
set).  By L3 the true optimum is <= max count for (A', delta') with delta' = delta_lo - 2EPS, attained by a greedy
from some left endpoint a* of A', which is a right endpoint hi_j and is among our starts.  Our positions are
<= the exact greedy positions (rounded-down steps, our allowed set larger, float comparisons exact), and our
termination limit is >= the exact one; by induction we place at least as many points.  []

## L4 Disjointness of shrunk forbidden arcs — PROVED (computer: `verify_L4.py`, arb)
For s, t in [E, R_I]: theta_II(s,t) >= theta(s) + theta(t) - delta_B.  Since max over a box of
f(s,t) = (s^2+t^2-4)/(2st) is attained at a corner (for fixed t, f is decreasing then increasing in s) and
theta is increasing, a single box suffices: certified margins at rho_test: n=15: 4.147 deg,
n=16: 3.725 deg.

## L5 Measure bound — PROVED (uses L4)
After L1, with B boundary points and interior radii s_j:  B delta_B + sum_j e(s_j) <= 2 pi.
*Proof.* U_b = (a_b - delta_B/2, a_b + delta_B/2) pairwise disjoint; for gap points F_j' = (psi_j - theta_j +
delta_B/2, psi_j + theta_j - delta_B/2) has length e(s_j); U_b cap F_j' = empty (else a_b within theta_j of
psi_j); F_j' cap F_l' = empty because |psi_j - psi_l|_circ >= theta_II(s_j, s_l) >= theta_j + theta_l - delta_B (L4).
With rho_test parameters the configuration satisfies the (weaker) constraints, and L4 was verified at rho_test,
so the bound holds with rho_test parameters as used by the code.  []

## L6 Radius ordering bound — PROVED (self-contained; literature values not needed)
Interior radii sorted s_0 >= ... >= s_{k-1}: s_j >= rho_{k-j} >= L_{k-j}, where the table L_m of rigorous
lower bounds is:
* m <= 7 (elementary): for rho < 2 the push-out lemma (R_I^2 = rho^2 - 4 < 0) moves every centre onto the
  circle (a centre at the origin would force all others to |c| >= 2 > rho), so m 2asin(1/rho) <= 2pi, i.e.
  rho_m >= 1/sin(pi/m) for m <= 6; and rho_7 >= rho_6 = 2.
* m = 8..13 (computer, `prove_radius_bounds.py`, log `out/final/radius_bounds.log`): the same rigorous B&B at
  rho_test = L_m := fl(rho_m^approx (1 - 1e-6)) finds no surviving box for any k, using only L_{m'} (m' < m);
  hence rho_m > L_m.  Values: L_8 = 2.3047625661976, L_9 = 2.6131233166268, L_10 = 2.8130228183725,
  L_11 = 2.9238014763587, L_12 = 3.0295989005143, L_13 = 3.2360647414318.
* m > 13: L_m := L_13 (monotonicity).
These also give the k-ranges: n=15: k <= 10 (L_11 > R_I = 2.8983); n=16: k <= 11 (L_12 > 3.0119).
(For comparison, the published optimal values are rho_10 = 2.8130256 (Pirl), rho_11 = 1/sin(pi/9) (Melissen),
rho_12 = 3.0296019 (Fodor), rho_13 = 1+sqrt5 (Fodor); they are NOT used.)

## L7 Local uniqueness lemma — PROVED (computer: `local_cert.py`)
Let x* be a configuration in the unit disk, B and C its boundary/contact sets, t* = d*^2, such that (verified):
 (a) x* lies in an explicit tiny box in which the active system has a unique solution (Krawczyk; for an
     overdetermined active set the mirror-symmetric reduced system, whose unique symmetric solution satisfies all
     active equations);
     all inactive constraints are strict on the box;
 (b) there are multipliers lambda_k > 0 (sum 1), mu_i > 0 with sum_j lambda_ij (p_i - p_j) = mu_i p_i;
 (c) sigma > 0 with |L delta| >= sigma |delta| for delta orthogonal to J x* (L = linearised active constraints).
Then with K^2 = sum_k 4 max(1, 1/lambda_k)^2 + sum_i (2/mu_i + 1)^2, delta_loc = sigma/K: every configuration x in
the closed unit disk with min distance >= d* and min_phi |R_phi x - x*|_2 < delta_loc is a rotation of x*.
*Proof.* (as before) phi minimising -> delta . J x* = 0; u_k = a_k.delta + |delta_i - delta_j|^2 >= 0,
v_i = b_i.delta - |delta_i|^2 >= 0; KKT identity gives sum lambda u + sum mu v = Q(delta) <= 2 eps^2; hence
|L delta| <= K eps^2; with |L delta| >= sigma eps: eps = 0 or eps >= delta_loc.  []
The lemma uses only the listed active constraints, so it holds for any positive multiplier vector satisfying
(b) (relevant when |B| + |C| > 2n).
Certified values: n=15: d* = 0.5679628677369514568307668140899832722(+-5e-38), delta_loc >= 3.079e-4;
n=16: d* = 0.5531852191443445298998869702087782279(+-1e-38), delta_loc >= 2.409e-4.

## L8 Survivors inside the uniqueness neighbourhood — PROVED (computer: `verify_final_arb.py`)
For every surviving canonical interior box (record case k): enumerate all assignments of the n-k boundary
points to allowed arcs (relaxed); exact Floyd–Warshall on the simple temporal network gives outer bounds of all
boundary angles; with the best relabelling/reflection, the maximal Euclidean distance (boundary points at radius
rho* exactly) to c* is < rho* delta_loc.  Results: n=15 (k=5):
D <= 2.12e-4 < 1.084e-3; n=16 (k=5): D <= 1.66e-4 < 8.71e-4.

## L9 Angular contraction — PROVED (code `contract_rig`)
If for all radii in the boxes theta_II(s_a, s_b) >= pm > 0 and psi_b lies in (phi_a - pm, plo_a + pm) (mod 2pi),
then every psi_a in [plo_a, phi_a] is within pm of psi_b, so |q_a - q_b| < 2: such psi_b can be removed.
pm is a rigorous lower bound (max of f at the 4 corners, rigorous arccos), endpoints rounded inward.  []

## L10 Interval primitives — PROVED (code `rigmath.py`, tests `test_rigmath.py`)
IEEE-754 +,-,*,/,sqrt are correctly rounded, so nextafter-widening encloses exact results; cos via
argument reduction with a bracketed 2pi and Taylor series with Lagrange remainder t^N/(2N)!; arccos via
arccos c = 2 arcsin(sqrt((1-c)/2)) (c >= 0; pi - arccos(-c) otherwise) and the arcsine series with positive
coefficients and geometric tail bound a_N y^{2N+1}/(1 - y^2).  Constants pi, 2pi and series coefficients are
float brackets computed with arb.  Tested against mpmath on 40,000+ inputs: no enclosure failure.

## L11 Assembly — see proof_attempt.md section 6.

---------------------------------------------------------------------------------------------------
## Structural observations (NUMERICALLY TESTED, not used in proofs)
* O1 (n=15): 5 delta_B + 10 theta(1/sin 36deg) = 2 pi exactly at rho*: the cyclic angular inequality is tight.
* O2: n=15 competitors: "4 pocket + 1 deep gap point" (d=0.567016), "2 pocket + 3 gap" (d=0.566527); all three
  top configurations have 10 boundary + 5 interior points.
* O3 (n=16): optimum "4 pocket points + 1 gap point" with 11 boundary points; next local optimum (10 boundary +
  6 interior) is 2.8% worse.
