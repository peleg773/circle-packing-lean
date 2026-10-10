import CirclePacking.Tower16Data

/-!
# The elimination identity for the 16-circle optimum

`f16` (here: its value `vF`) is the last contact equation `(a - b)² + c² = 4` of the symmetry-reduced
system, scaled to a polynomial in the tower (see `Bridge16.lean`).  The kernel checks, step by step from
literal intermediate values, that its iterated norm down to `ℤ[q]` equals
`2¹⁰⁰ H16(q)² (1 + 2q)²⁴ (q - 1)⁹⁶`.  Since a norm of a vanishing element vanishes, a solution of the
reduced system has `H16(q) = 0` (`H16_eval_eq_zero`).
-/

namespace CirclePacking.Tw16

local infixl:65 " +' " => add4
local infixl:70 " *' " => mul4
local prefix:max "-'" => neg4

def kq : K4 := cst [0, 1]
def kL : K4 := cst [1, -1]

/-! ### The kernel checks -/

set_option maxRecDepth 100000

theorem vA_ok : beq4 (-'(gR *' cst zT5) +' -'(kL *' gwa)) vA = true := by decide +kernel
theorem vD_ok : beq4 (-'(gR *' kq) +' kL *' gwd) vD = true := by decide +kernel
theorem vDD_ok : beq4 ((vA +' gR *' cst zT3) +' -'((vA +' -'vD) *' gt *' cst zU2)) vDD = true := by
  decide +kernel
theorem vNb_ok : beq4 ((vA *' vA +' -'(gR *' gR)) +' gt *' cst zU2 *' (vD *' vD +' kL *' kL +' -'(vA *' vA)))
    vNb = true := by decide +kernel
theorem vX1_ok : beq4 (cst [2] *' vDD *' vA +' -'vNb) vX1 = true := by decide +kernel
theorem vX2_ok : beq4 ((vA +' -'vD) *' vNb +' vDD *' (vD *' vD +' kL *' kL +' -'(vA *' vA))) vX2 = true := by
  decide +kernel
theorem vF_ok : beq4 (kL *' kL *' (vX1 *' vX1) +' vX2 *' vX2 +' -'(cst [16] *' kL *' kL *' kL *' kL *' vDD *' vDD))
    vF = true := by decide +kernel
theorem vN4_ok : beq3 (nrm4 vF) vN4 = true := by decide +kernel
theorem vN3_ok : beq2 (nrm3 vN4) vN3 = true := by decide +kernel
theorem vN2_ok : beq1 (nrm2 vN3) vN2 = true := by decide +kernel
theorem vN1_ok : ZPoly.beqZ (nrm1 vN2) vN1 = true := by decide +kernel
theorem vH2_ok : ZPoly.beqZ (ZPoly.mul H16coeffs H16coeffs) vH2 = true := by decide +kernel
theorem vP_ok : ZPoly.beqZ (ZPoly.mul (ZPoly.pow [1, 2] 24) (ZPoly.pow [-1, 1] 96)) vP = true := by
  decide +kernel
/-- **The elimination identity**: the norm of `f16` is `2¹⁰⁰ H16² (1 + 2q)²⁴ (q - 1)⁹⁶`. -/
theorem vN1_eq : ZPoly.beqZ vN1 (ZPoly.smul (2 ^ 100) (ZPoly.mul vH2 vP)) = true := by decide +kernel

end CirclePacking.Tw16
