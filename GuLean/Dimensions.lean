import Mathlib

/-!
# The dimension counts of Sections 3 and 8

These are the numerical coincidences the shiab construction leans on. They are all true.
-/

namespace GU.Dimensions

/-- §3: the bundle of metrics over a 4-manifold has a 10-dimensional fibre
(symmetric 4×4 matrices), so the observerse `Y` is 14-dimensional. -/
theorem dim_observerse : 4 + 4 * (4 + 1) / 2 = 14 := by decide

/-- Dirac spinors in dimension 14 have dimension `2^7 = 128`. -/
theorem dim_spinors : 2 ^ (14 / 2) = 128 := by decide

/-- Eq. (8.2)–(8.3): `dim Λ*(ℝ¹⁴) = 2¹⁴ = 128² = dim ℝ(128)`. -/
theorem dim_exterior_eq_dim_matrices : ∑ i ∈ Finset.range 15, Nat.choose 14 i = 128 ^ 2 := by
  decide

/-- Eq. (8.5): the degrees `2, 6, 10, 14` and `1, 5, 9, 13` add up to
`dim so(64,64) = 128·127/2`. -/
theorem dim_so_part :
    (Nat.choose 14 2 + Nat.choose 14 6 + Nat.choose 14 10 + Nat.choose 14 14) +
      (Nat.choose 14 1 + Nat.choose 14 5 + Nat.choose 14 9 + Nat.choose 14 13) =
      128 * 127 / 2 := by decide

/-- Eq. (8.6): the remaining degrees `0, 3, 4, 7, 8, 11, 12` add up to
`dim u(64,64) − dim so(64,64) = 128·129/2`. -/
theorem dim_u_mod_so_part :
    Nat.choose 14 0 + Nat.choose 14 3 + Nat.choose 14 4 + Nat.choose 14 7 + Nat.choose 14 8 +
      Nat.choose 14 11 + Nat.choose 14 12 = 128 * 129 / 2 := by decide

/-- `dim_ℝ u(64,64) = 128²`, matching the exterior algebra. -/
theorem dim_u : 128 * 127 / 2 + 128 * 129 / 2 = 128 ^ 2 := by decide

/-- `dim Spin(14) = 91`, nowhere near `2¹⁴`. This is why the Nguyen–Polya response notes
that shrinking the structure group to the spin group, which would avoid the anomaly they
describe, leaves nothing to identify with the exterior algebra. -/
theorem dim_spin14_lt : Nat.choose 14 2 = 91 ∧ 91 < 2 ^ 14 := by decide

end GU.Dimensions
