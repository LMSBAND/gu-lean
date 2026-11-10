import Mathlib

/-!
# Section 3.5: which degrees of the Clifford algebra form which Lie algebra

Eqs. (3.21), (3.22), (3.26), (3.27) and (8.5), (8.6) identify Lie algebras with sums of
exterior powers inside `Cl(7,7)`. Footnote 3 of the draft says of (3.27): "This decomposition
was taken from a decades old file and should be checked by someone more current".

It is checked here, as bookkeeping, against the standard degree rule for Clifford products:
for `a` of degree `p` and `b` of degree `q`, the product `a b` has components in degrees
`p + q − 2k`, and the component of `b a` in that degree is `(−1)^(pq − k)` times that of
`a b`. So the commutator `[a, b]` keeps exactly the `k` with `pq − k` odd.

The rule itself is an input here, not derived from Mathlib's `CliffordAlgebra`.
-/

namespace GU.CliffordGrading

/-- `k` survives in the commutator of degrees `p` and `q`. -/
def Survives (p q k : ℕ) : Prop :=
  k ≤ p ∧ k ≤ q ∧ ((p % 2 = 1 ∧ q % 2 = 1 → k % 2 = 0) ∧ (¬(p % 2 = 1 ∧ q % 2 = 1) → k % 2 = 1))

/-- CHECKED. Eq. (3.22): degrees ≡ 2 mod 4 are closed under commutator. -/
theorem gl64_closed (p q k : ℕ) (hp : p % 4 = 2) (hq : q % 4 = 2) (h : Survives p q k) :
    (p + q - 2 * k) % 4 = 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  omega

/-- CHECKED. Eq. (3.26)/(8.5): degrees ≡ 1, 2 mod 4 are closed under commutator. -/
theorem so_closed (p q k : ℕ) (hp : p % 4 = 1 ∨ p % 4 = 2) (hq : q % 4 = 1 ∨ q % 4 = 2)
    (h : Survives p q k) : (p + q - 2 * k) % 4 = 1 ∨ (p + q - 2 * k) % 4 = 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  omega

/-- CHECKED. Eq. (3.27)/(8.6): the bracket of a degree ≡ 1, 2 element with `i` times a degree
≡ 0, 3 element is `i` times a degree ≡ 0, 3 element. -/
theorem u_mixed (p q k : ℕ) (hp : p % 4 = 1 ∨ p % 4 = 2) (hq : q % 4 = 0 ∨ q % 4 = 3)
    (h : Survives p q k) : (p + q - 2 * k) % 4 = 0 ∨ (p + q - 2 * k) % 4 = 3 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  omega

/-- CHECKED. Eq. (3.27)/(8.6): the bracket of two `i`-twisted degree ≡ 0, 3 elements has
degree ≡ 1, 2 (and `i · i = −1` is real). So (3.27) is closed under commutator. -/
theorem u_twisted (p q k : ℕ) (hp : p % 4 = 0 ∨ p % 4 = 3) (hq : q % 4 = 0 ∨ q % 4 = 3)
    (h : Survives p q k) : (p + q - 2 * k) % 4 = 1 ∨ (p + q - 2 * k) % 4 = 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  omega

/-- CHECKED. Eq. (3.21): `dim so(7,7) = dim Λ²`. -/
theorem dim_so77 : 14 * 13 / 2 = Nat.choose 14 2 := by decide

/-- CHECKED. Eq. (3.22): the degrees 2, 6, 10, 14 have total dimension `64² = dim gl(64, ℝ)`. -/
theorem dim_gl64 :
    Nat.choose 14 2 + Nat.choose 14 6 + Nat.choose 14 10 + Nat.choose 14 14 = 64 ^ 2 := by
  decide

end GU.CliffordGrading
