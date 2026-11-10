import GuLean.Inhomogeneous

/-!
# Sections 8–9: the shiab operator and the field equation

Eq. (9.8) of the draft, the first-order bosonic field equation, reads

    ⊙_ε F_{A_ω} = − ∗ κ₁ T_ω .

Sections 5–7 supply `T`. Everything else on that line is listed in `FieldEquationInputs`
below. The draft does not supply a term of that type. What it says about the operator:

* §8: "a Shiab contraction operator might look like: [eq. 8.1] or perhaps a sum of such
  terms"
* §8: "The author is no longer in a position to go chasing after the complete picture"
* Definition 8.1 names the `Φᵢ` as "a basis for the invariant subspaces" of
  `[Λⁱ(ℝ^{7,7}) ⊗ u(64,64)]^{Spin(7,7)}` without computing those subspaces, their
  dimensions, or a normalisation.
* §8.2: "the author is no longer conversant in that language and has been unable to locate
  the notes from decades ago that originally picked out the operator of choice"
* §9.1, footnote 10: "The Shiab operator that he settled on (but cannot yet now locate)"

So the equation can be stated in Lean only with the operator as a free parameter, and the
gauge covariance of the equation can be proved only as an implication from properties of
that parameter which the draft asserts and does not prove.
-/

namespace GU

variable {H N : Type*} [Group H] [AddCommGroup N] [DistribMulAction H N]

/-- What eq. (9.8) needs beyond Sections 5–7.

`Ω2` stands for `Ω²(Y, ad)` and `Ωd1` for `Ω^{d−1}(Y, ad)`. -/
structure FieldEquationInputs (H N Ω2 Ωd1 : Type*) [Group H] [AddCommGroup N]
    [DistribMulAction H N] [AddCommGroup Ω2] [DistribMulAction H Ω2] [AddCommGroup Ωd1]
    [Module ℝ Ωd1] [DistribMulAction H Ωd1] where
  /-- `F_{A_ω}`, the curvature of `A₀ + ϖ`. Standard; statable once connections on a spinor
  bundle over `Y` exist in Mathlib. -/
  curvature : Inhomog H N → Ω2
  /-- The Hodge star `Ω¹ → Ω^{d−1}`. Standard. -/
  star : N →+ Ωd1
  /-- Eq. (9.2): the shiab operator `⊙_ε : Ω² → Ω^{d−1}`. NOT DEFINED IN THE DRAFT. -/
  shiab : H → Ω2 →+ Ωd1
  /-- The constant `κ₁`. Not given a value in the draft. -/
  κ : ℝ

variable {Ω2 Ωd1 : Type*} [AddCommGroup Ω2] [DistribMulAction H Ω2] [AddCommGroup Ωd1]
  [Module ℝ Ωd1] [DistribMulAction H Ωd1]

/-- Eq. (9.7)–(9.8): `Υ_ω = ⊙_ε F_{A_ω} + κ₁ ∗ T_ω`. The field equation is `Υ_ω = 0`. -/
def upsilon (d : Cocycle H N) (I : FieldEquationInputs H N Ω2 Ωd1) (g : Inhomog H N) : Ωd1 :=
  I.shiab g.ε (I.curvature g) + I.κ • I.star (torsion d g)

/-- The draft's central claim, that the field equation is gauge covariant, as far as it can
be checked: it follows from three hypotheses. The first two are standard facts. The third
is a property of an operator the draft does not define. -/
theorem upsilon_equivariant (d : Cocycle H N) (I : FieldEquationInputs H N Ω2 Ωd1)
    [SMulCommClass ℝ H Ωd1]
    (curvature_equivariant : ∀ g h, I.curvature (g * tauPlus d h) = h⁻¹ • I.curvature g)
    (star_equivariant : ∀ (h : H) (n : N), I.star (h • n) = h • I.star n)
    (shiab_equivariant : ∀ (ε h : H) (ξ : Ω2), I.shiab (ε * h) (h⁻¹ • ξ) = h⁻¹ • I.shiab ε ξ)
    (g : Inhomog H N) (h : H) :
    upsilon d I (g * tauPlus d h) = h⁻¹ • upsilon d I g := by
  have e1 : (g * tauPlus d h).ε = g.ε * h := rfl
  rw [upsilon, upsilon, torsion_mul_tauPlus, curvature_equivariant, star_equivariant, e1,
    shiab_equivariant, smul_add, smul_comm I.κ h⁻¹]

/-! ## Definition 8.1 does not single out the forms `Φᵢ`

Definition 8.1 takes `Φᵢ` from the `Spin(7,7)`-invariants of `Λⁱ ⊗ u(64,64)`, that is, from
the equivariant maps out of the `i`-forms into `u(64,64)` under conjugation. The theorem below
shows that any such map `Φ` yields a second one, `Φ · λ`, for any `λ` commuting with the group.
In `Cl(7,7)` the volume element `λ` commutes with `Spin(7,7)`. For `Φ₁` the map `v ↦ γ(v)` has
values in degree 1 and `v ↦ γ(v) λ` in degree 13, and the draft's own eq. (8.5) places both
degrees inside `u(64,64)`. So the space `Φ₁` is taken from is at least two-dimensional, and
eq. (9.3), which uses "the" `Φ₁` and `Φ₂`, is not determined by Definition 8.1 even up to scale.

The equivariance step is checked below. The facts about `Cl(7,7)` quoted in this paragraph are
standard and are not formalized here. -/

/-- CHECKED. An equivariant map into an algebra, multiplied by an element commuting with the
group, is again equivariant. -/
theorem equivariant_mul_commuting {G V A : Type*} [Group G] [Ring A] (conj : G →* Aˣ)
    (ρ : G → V → V) (Φ : V → A)
    (hΦ : ∀ g v, Φ (ρ g v) = conj g * Φ v * ↑(conj g)⁻¹)
    (lam : A) (hlam : ∀ g, Commute (↑(conj g) : A) lam) (g : G) (v : V) :
    Φ (ρ g v) * lam = conj g * (Φ v * lam) * ↑(conj g)⁻¹ := by
  have h := (hlam g).units_inv_left
  simp only [hΦ, mul_assoc, h.eq]

/-! ## Filling the gap from the literature: equivariance is free

The "ship in a bottle" recipe of eq. (8.1) is `⊙_ε ξ = [ε⁻¹ Φ ε ∧ ∗ξ]`. For ANY fixed `Φ` and
any equivariant bilinear pairing, this has the equivariance property `upsilon_equivariant`
needs. So that hypothesis can be discharged without knowing `Φ`, and equivariance places no
constraint on which `Φ` is meant. -/

/-- CHECKED. Conjugating a fixed element by `ε` always yields an equivariant operator. -/
theorem conjugated_pairing_equivariant {H P Ω2 Ωd1 : Type*} [Group H] [MulAction H P]
    [MulAction H Ω2] [MulAction H Ωd1] (B : P → Ω2 → Ωd1)
    (hB : ∀ (h : H) (φ : P) (ξ : Ω2), B (h • φ) (h • ξ) = h • B φ ξ) (Φ : P)
    (ε h : H) (ξ : Ω2) :
    B ((ε * h)⁻¹ • Φ) (h⁻¹ • ξ) = h⁻¹ • B (ε⁻¹ • Φ) ξ := by
  rw [mul_inv_rev, mul_smul, hB]

end GU
