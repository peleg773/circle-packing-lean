# Literature and status (relevant items only)

Detailed notes with per-claim provenance: `literature_src/LIT_AGENT_NOTES.md`. PDFs/texts in `literature_src/`.

## Status as of 2026-10-09
| n | best known d_n (unit disk) | status | first found |
|---|---|---|---|
| 13 | (sqrt5-1)/2 = 0.6180339887 | proved (Fodor 2003) | |
| 14 | 0.6008841611 | proved: Fodor 2003 (Stud. Univ. Zilina Math. Ser. 16, 25-34; not accessible), Ekanayake-LaFountain 2024 (relies on Desmos graphs); Packomania does not bold it | Goldberg 1971 |
| **15** | 0.5679628677369514568... (D5, exact form below) | **open** | Kravitz 1967 / Pirl 1969 |
| **16** | 0.5531852191443445299... | **open** | Goldberg 1971 |
| 17 | 0.5274214663545747216... | open | Reis 1975 |
| 18 | 2 sin(pi/12) = 0.5176380902 | open (= d_19, proven only for 19) | Kravitz 1967 / Pirl 1969; GLNO 1998 many variants |
| 19 | 2 sin(pi/12) | proved (Fodor 1999) | |

**Update 2026-10-11.** n = 15 and 16: proved and Lean-verified in this repository (published 10 October 2026).
n = 18: proved and Lean-verified in this repository (added 11 October 2026).
Sources checked: Packomania (last update 25-Dec-2024; bold = proven only for N <= 13 and 19), NumberDB T394
(open: 15, 16, 17, 18, 20), Wikipedia, arXiv API searches (no paper on n >= 15 optimality),
Semantic Scholar / OpenAlex citation chains of Fodor 1999/2003, Melissen 1994, GLNO 1998, E-L 2020, Pirl 1969
(no proof claimed for n >= 15), OEIS A384851 (n=14 constant only), arXiv:2609.15554 (irrelevant: nested annuli),
Pchelina 2026 survey (all circle-container proofs so far by hand).  A Zenodo record (Moki&Julio, 2026) announces a
computer-assisted proof for 16 circles in an *equilateral triangle* (different container).  No computer-assisted
proof for the circular container was found.

## Primary references used
* U. Pirl, Der Mindestabstand von n in der Einheitskreisscheibe gelegenen Punkten, Math. Nachr. 40 (1969)
  111-124. (n <= 10; conjectured packings up to 19.)  [not accessed; secondary statements only]
* H. Melissen, Densest packing of eleven congruent circles in a circle, Geom. Dedicata 50 (1994) 15-25. [abstract]
* F. Fodor, The densest packing of 19 congruent circles in a circle, Geom. Dedicata 74 (1999) 139-145,
  doi:10.1023/A:1005091317243. [not accessible; tools quoted in his n=12/13 papers]
* F. Fodor, The densest packing of 12 congruent circles in a circle, Beitr. Algebra Geom. 41 (2000) 401-409
  (EMIS). [read]
* F. Fodor, The densest packing of 13 congruent circles in a circle, Beitr. Algebra Geom. 44 (2003) 431-440
  (EMIS). [read]
* D.B. Ekanayake, D.J. LaFountain, Tight partitions for packing circles in a circle, Ital. J. Pure Appl. Math. 51
  (2024) 115-136, https://ijpam.uniud.it/online_issue/202451/10%20Ekanayake-LaFountain.pdf [read]
* D.B. Ekanayake, M.M. Ranpatidewage, D.J. LaFountain, Optimal packings for filled rings of circles,
  Appl. Math. 65 (2020) 1-22, doi:10.21136/AM.2020.0244-19. [skimmed]
* R.L. Graham, B.D. Lubachevsky, K.J. Nurmela, P.R.J. Ostergard, Dense packings of congruent circles in a circle,
  Discrete Math. 181 (1998) 139-154, doi:10.1016/S0012-365X(97)00050-2. [read]
* P. Bateman, P. Erdos, Geometrical extrema suggested by a lemma of Besicovitch, Amer. Math. Monthly 58 (1951)
  306-314. [read]  (Lemma 1 = annulus angle lemma; our theta/delta_B are its unit-circle version.)
* E. Specht, Packomania, https://www.packomania.com/cci/cci.html (coordinates used: txt/cciN.txt).

## Techniques learned (what our proof reuses / differs from)
* Bateman-Erdos/Fodor angle lemma: two points in an annulus subtend a minimal angle; Fodor's n=12,13 proofs
  split at radius R - 1/R, count outer points, then use Lemma 2 (push inner points outward) and case analysis
  verified by Mathematica plots.  Our push-out lemma L1 is the analogous normalisation, but at radius
  sqrt(rho^2 - 4), which makes the reduction to a 1-D boundary problem EXACT.
* Ekanayake-LaFountain: rings, "gap circles" (our "gap points", threshold E = sqrt(rho^2-1) - sqrt3),
  angular-support sums; several steps are informal (Conditions A-C, Desmos graphs).
* The literature agent observed (and we confirm, lemmas.md O1) that the n = 15 optimum is an exact equality case
  of the Fodor/Bateman-Erdos angle calculus: 5 delta_B + 10 theta(1/sin 36deg) = 2 pi.
* d_15 is a root of 41 d^8 - 200 d^6 + 285 d^4 - 150 d^2 + 25 (agent; verified numerically, see experiments).
