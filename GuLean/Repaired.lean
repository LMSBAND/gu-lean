import GuLean.Inhomogeneous

/-!
# Sections 5–7, repaired

The draft's footnote 9 says "the interested community is welcome to send bug fixes". This
file is one.

Change three signs:

* eq. (6.4):  `τ(h) = (h, +h⁻¹ (d_{A₀} h))`
* eq. (6.11): `π(ε, ϖ) = ε ϖ ε⁻¹ − (d_{A₀} ε) ε⁻¹`
* eq. (6.15): `(ε, ϖ) · γ = ε (ϖ + γ) ε⁻¹ − (d_{A₀} ε) ε⁻¹`

and leave eq. (6.9), the "flipped" map `τ̂`, as printed. Then every lemma of Sections 6 and 7
is true, and `τ` and `τ̂` are two different maps, as the text intends: `τ̂` parameterizes the
stabilizer of `A₀`, and `τ` is the subgroup under which the torsion is equivariant.

This is the reading used everywhere else in this project when the draft is given the benefit
of the doubt.
-/

namespace GU.Repaired

variable {H N : Type*} [Group H] [AddCommGroup N] [DistribMulAction H N] (d : Cocycle H N)

/-- Eq. (6.15) with the sign changed. -/
def leftAct (g : Inhomog H N) (γ : N) : N := g.ε • (g.ϖ + γ) - g.ε • d.c g.ε

/-- Lemma 6.1 holds. -/
theorem tau_mul (h₁ h₂ : H) : tauPlus d (h₁ * h₂) = tauPlus d h₁ * tauPlus d h₂ :=
  tauPlus_mul d h₁ h₂

/-- §6.2 holds: the stabilizer of `A₀` is the image of the flipped map. -/
theorem stabilizer (g : Inhomog H N) : connAct d 0 g = 0 ↔ g = tauHat d g.ε :=
  connAct_zero_eq_zero_iff d g

/-- Right multiplication by the tilted group is an honest gauge transformation of the
connection `A₀ + ϖ`. -/
theorem tau_acts_by_gauge (g : Inhomog H N) (h : H) :
    (g * tauPlus d h).ϖ = gaugeAct d g.ϖ h := rfl

/-- Lemma 6.3 holds. -/
theorem proj_invariant (g : Inhomog H N) (h : H) :
    projFixed d (g * tauPlus d h) = projFixed d g :=
  projFixed_mul_tauPlus d g h

/-- Lemma 6.4 holds. -/
theorem leftAct_mul (g₁ g₂ : Inhomog H N) (γ : N) :
    leftAct d (g₁ * g₂) γ = leftAct d g₁ (leftAct d g₂ γ) := by
  simp only [leftAct, Inhomog.mul_ε, Inhomog.mul_ϖ, d.leibniz, smul_add, smul_sub, mul_smul,
    smul_inv_smul]
  abel

/-- And it is the action the projection induces from left multiplication, which is what the
sentence before Lemma 6.4 claims. -/
theorem proj_mul (g₁ g₂ : Inhomog H N) :
    projFixed d (g₁ * g₂) = leftAct d g₁ (projFixed d g₂) := by
  simp only [projFixed, torsion, leftAct, Inhomog.mul_ε, Inhomog.mul_ϖ, d.leibniz, smul_add,
    smul_sub, mul_smul, smul_inv_smul]
  abel

/-- Lemma 6.5 holds. -/
theorem biConn_equivariant (g : Inhomog H N) (h : H) :
    biConn d (g * tauPlus d h) = (gaugeAct d (biConn d g).1 h, gaugeAct d (biConn d g).2 h) :=
  biConn_mul_tauPlus d g h

/-- Lemma 7.2 holds. -/
theorem torsion_equivariant (g : Inhomog H N) (h : H) :
    torsion d (g * tauPlus d h) = h⁻¹ • torsion d g :=
  torsion_mul_tauPlus d g h

end GU.Repaired
