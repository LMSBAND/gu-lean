import Mathlib

/-!
# Section 3.1, 3.5 and 4: signatures

The fibre of the metric bundle over a point of `X⁴` is the space of symmetric 4×4 matrices.
Eq. (3.8) puts the "Frobenius" form `⟨A, B⟩ = Tr(g⁻¹ A g⁻¹ B)` on it. This file checks the
signature claims built on that form.
-/

namespace GU.Signature

open Matrix

/-- A metric of signature (1,3) in an orthonormal frame. It is its own inverse. -/
def η : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![1, -1, -1, -1]

/-- Eq. (3.8) at the point `η`. -/
def frob (A B : Matrix (Fin 4) (Fin 4) ℝ) : ℝ := (η * A * η * B).trace

/-- CHECKED. In the coordinates `A i j`, `i ≤ j`, on symmetric matrices the form of eq. (3.8)
is diagonal with seven coefficients of one sign and three of the other: signature (7,3). -/
theorem frob_self (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.IsSymm) :
    frob A A =
      (A 0 0 ^ 2 + A 1 1 ^ 2 + A 2 2 ^ 2 + A 3 3 ^ 2
        + 2 * A 1 2 ^ 2 + 2 * A 1 3 ^ 2 + 2 * A 2 3 ^ 2)
      - (2 * A 0 1 ^ 2 + 2 * A 0 2 ^ 2 + 2 * A 0 3 ^ 2) := by
  have h10 : A 1 0 = A 0 1 := hA.apply 0 1
  have h20 : A 2 0 = A 0 2 := hA.apply 0 2
  have h30 : A 3 0 = A 0 3 := hA.apply 0 3
  have h21 : A 2 1 = A 1 2 := hA.apply 1 2
  have h31 : A 3 1 = A 1 3 := hA.apply 1 3
  have h32 : A 3 2 = A 2 3 := hA.apply 2 3
  simp [frob, η, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal,
    h10, h20, h30, h21, h31, h32]
  ring

/-- CHECKED. The trace direction (the metric itself) lies on the side with seven. So the
traceless part has signature (6,3), and the form of eq. (3.8) as defined gives (7,3). The
draft's (4,6) is obtained by reversing the sign on the trace direction by hand, which the
draft says is a choice (§3.1, footnote 2). -/
theorem frob_trace_direction : frob η η = 4 := by
  simp [frob, η, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal]
  norm_num

/-- CHECKED. The general signature formula printed above eq. (3.9): the count of same-sign
off-diagonal and traceless diagonal directions. -/
theorem traceless_formula (n i : ℤ) :
    2 * (n - 1) + i * (i - 1) + (n - i) * (n - i - 1) = n ^ 2 + 2 * i ^ 2 - 2 * i * n + n - 2 := by
  ring

/-- CHECKED. Eq. (3.9) at `i = 1`, `n = 4`: traceless part (3,6), total (4,6). -/
theorem eq_3_9 : 1 * 4 - 1 ^ 2 = 3 ∧ (4 ^ 2 + 2 * 1 ^ 2 - 2 * 1 * 4 + 4 - 2) / 2 = 6 := by decide

/-- CHECKED. §3.5: the six totals listed for fibre ⊕ base. -/
theorem section_3_5_sums :
    (3 + 1, 7 + 3) = (4, 10) ∧ (7 + 1, 3 + 3) = (8, 6) ∧
    (4 + 1, 6 + 3) = (5, 9) ∧ (6 + 1, 4 + 3) = (7, 7) ∧ (4 + 3, 6 + 1) = (7, 7) := by decide

/-- CHECKED. Eq. (4.2)–(4.3): Dirac spinors of the 10-dimensional normal bundle have
dimension 32, Weyl spinors 16. -/
theorem eq_4_3 :
    2 ^ ((1 ^ 2 + 3 ^ 2 + 2 * 1 * 3 + 1 + 3) / 4) = 32 ∧
    2 ^ ((1 ^ 2 + 3 ^ 2 + 2 * 1 * 3 + 1 + 3 - 4) / 4) = 16 := by decide

end GU.Signature
