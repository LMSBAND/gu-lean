import Mathlib

/-!
# Sections 5–7 of "Geometric Unity: Author's Working Draft v1.0" (April 1st 2021)

The inhomogeneous gauge group, the tilted map, and the augmented torsion.

Everything in these sections is algebra on three pieces of data, and the draft's own
proofs use nothing else:

* a group `H`                      (the gauge group, eq. 5.3)
* an additive group `N` on which `H` acts   (ad-valued 1-forms, eq. 5.5)
* a map `c : H → N`, `c h = h⁻¹ (d_{A₀} h)`, obeying the Leibniz rule.

We write `h • n` for `h n h⁻¹`, so the draft's `Aut(ε⁻¹, ϖ) = ε⁻¹ ϖ ε` is `ε⁻¹ • ϖ`.

Any theorem proved here holds in the draft's geometric setting. Any statement refuted
here from these axioms cannot be proved by the draft's argument, and the explicit error
terms show it is false there whenever some gauge transformation is not covariantly
constant.
-/

namespace GU

/-- Definition 5.1. The underlying set of `G = H ⋉ N`: pairs `(ε, ϖ)`. -/
@[ext] structure Inhomog (H N : Type*) where
  ε : H
  ϖ : N

variable {H N : Type*} [Group H] [AddCommGroup N] [DistribMulAction H N]

namespace Inhomog

/-- Eq. (5.9): `(ε₁, ϖ₁) · (ε₂, ϖ₂) = (ε₁ ε₂, ε₂⁻¹ ϖ₁ ε₂ + ϖ₂)`. -/
instance : Mul (Inhomog H N) := ⟨fun a b => ⟨a.ε * b.ε, b.ε⁻¹ • a.ϖ + b.ϖ⟩⟩
instance : One (Inhomog H N) := ⟨⟨1, 0⟩⟩
instance : Inv (Inhomog H N) := ⟨fun a => ⟨a.ε⁻¹, -(a.ε • a.ϖ)⟩⟩

@[simp] theorem mul_ε (a b : Inhomog H N) : (a * b).ε = a.ε * b.ε := rfl
@[simp] theorem mul_ϖ (a b : Inhomog H N) : (a * b).ϖ = b.ε⁻¹ • a.ϖ + b.ϖ := rfl
omit [DistribMulAction H N] in
@[simp] theorem one_ε : (1 : Inhomog H N).ε = 1 := rfl
omit [DistribMulAction H N] in
@[simp] theorem one_ϖ : (1 : Inhomog H N).ϖ = 0 := rfl
@[simp] theorem inv_ε (a : Inhomog H N) : a⁻¹.ε = a.ε⁻¹ := rfl
@[simp] theorem inv_ϖ (a : Inhomog H N) : a⁻¹.ϖ = -(a.ε • a.ϖ) := rfl

/-- CHECKED. Eq. (5.9) does define a group. -/
instance : Group (Inhomog H N) where
  mul_assoc a b c := by ext <;> simp [mul_assoc, mul_smul, add_assoc]
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  inv_mul_cancel a := by ext <;> simp

end Inhomog

/-- The map `h ↦ h⁻¹ (d_{A₀} h)` together with the only property of it the draft uses
(the step from the first to the second line of eq. 6.5). -/
structure Cocycle (H N : Type*) [Group H] [AddCommGroup N] [DistribMulAction H N] where
  c : H → N
  leibniz : ∀ h₁ h₂, c (h₁ * h₂) = h₂⁻¹ • c h₁ + c h₂

variable (d : Cocycle H N)

@[simp] theorem Cocycle.map_one : d.c 1 = 0 := by
  have := d.leibniz 1 1
  simpa using this

/-! ## The maps, exactly as printed -/

/-- Eq. (6.4): `τ_{A₀}(h) = (h, −h⁻¹ (d_{A₀} h))`. The draft's tilted map. -/
def tauMinus (h : H) : Inhomog H N := ⟨h, -d.c h⟩

/-- Eq. (6.9): the "flipped" map `τ̂₀(h) = (h, −h⁻¹ d₀ h)`. -/
def tauHat (h : H) : Inhomog H N := ⟨h, -d.c h⟩

/-- The opposite sign, `(h, +h⁻¹ (d_{A₀} h))`. This is the tilted map of the video
presentation as transcribed by Nguyen–Polya (their Section 2.2), and it is what the second lines of the draft's proofs
(6.20) and (7.4) silently switch to. -/
def tauPlus (h : H) : Inhomog H N := ⟨h, d.c h⟩

/-- Eq. (6.2) with `A = A₀ + α`: right action of `G` on connections,
`α · (ε, ϖ) = ε⁻¹ α ε + ε⁻¹ (d_{A₀} ε) + ϖ`. -/
def connAct (α : N) (g : Inhomog H N) : N := g.ε⁻¹ • α + d.c g.ε + g.ϖ

/-- The ordinary gauge action of `h ∈ H` on a connection `A₀ + α`. -/
def gaugeAct (α : N) (h : H) : N := h⁻¹ • α + d.c h

/-- Eq. (6.11): `π_{A₀}(ε, ϖ) = ε ϖ ε⁻¹ + (d_{A₀} ε) ε⁻¹`. -/
def proj (g : Inhomog H N) : N := g.ε • g.ϖ + g.ε • d.c g.ε

/-- Eq. (6.15): `(ε, ϖ) · γ = ε (ϖ + γ) ε⁻¹ + (d_{A₀} ε) ε⁻¹`. -/
def leftAct (g : Inhomog H N) (γ : N) : N := g.ε • (g.ϖ + γ) + g.ε • d.c g.ε

/-- Eqs. (6.18)–(6.19), in `A₀`-coordinates: `μ(ε, ϖ) = (A₀ + ϖ, A₀ + ε⁻¹ (d_{A₀} ε))`. -/
def biConn (g : Inhomog H N) : N × N := (g.ϖ, d.c g.ε)

/-- Eq. (7.3): the augmented torsion `T_g = ϖ − ε⁻¹ (d_{A₀} ε)`. -/
def torsion (g : Inhomog H N) : N := g.ϖ - d.c g.ε

/-! ## What checks -/

/-- CHECKED. Eq. (6.2)/(5.10) is a right action of `G`. -/
theorem connAct_mul (α : N) (g₁ g₂ : Inhomog H N) :
    connAct d α (g₁ * g₂) = connAct d (connAct d α g₁) g₂ := by
  simp only [connAct, Inhomog.mul_ε, Inhomog.mul_ϖ, d.leibniz, mul_inv_rev, mul_smul, smul_add]
  abel

/-- CHECKED. Lemma 6.1: the tilted map as printed is a homomorphism. -/
theorem tauMinus_mul (h₁ h₂ : H) : tauMinus d (h₁ * h₂) = tauMinus d h₁ * tauMinus d h₂ := by
  ext
  · rfl
  · simp only [tauMinus, Inhomog.mul_ϖ, d.leibniz, smul_neg]
    abel

/-- CHECKED. So is the opposite-sign map. -/
theorem tauPlus_mul (h₁ h₂ : H) : tauPlus d (h₁ * h₂) = tauPlus d h₁ * tauPlus d h₂ := by
  ext
  · rfl
  · simp only [tauPlus, Inhomog.mul_ϖ, d.leibniz]

/-- CHECKED. §6.2: the stabilizer of `A₀` is exactly the image of eq. (6.9). -/
theorem connAct_zero_eq_zero_iff (g : Inhomog H N) :
    connAct d 0 g = 0 ↔ g = tauHat d g.ε := by
  constructor
  · intro h
    ext
    · rfl
    · simp only [connAct, smul_zero, zero_add] at h
      simp only [tauHat]
      exact eq_neg_of_add_eq_zero_right h
  · intro h
    rw [h]
    simp [connAct, tauHat]

/-- The "tilted" map (6.4) and the "flipped" map (6.9) are the same map as printed.
The draft presents them as two different objects. -/
theorem tauMinus_eq_tauHat : (tauMinus d : H → Inhomog H N) = tauHat d := rfl

/-- CHECKED. Lemma 6.3 as printed: `π` is invariant under the printed tilted map. -/
theorem proj_mul_tauMinus (g : Inhomog H N) (h : H) :
    proj d (g * tauMinus d h) = proj d g := by
  simp only [proj, tauMinus, Inhomog.mul_ε, Inhomog.mul_ϖ, d.leibniz, smul_add, smul_neg,
    mul_smul, smul_inv_smul]
  abel

/-- CHECKED. Lemma 6.4: eq. (6.15) is a left action of `G`. -/
theorem leftAct_mul (g₁ g₂ : Inhomog H N) (γ : N) :
    leftAct d (g₁ * g₂) γ = leftAct d g₁ (leftAct d g₂ γ) := by
  simp only [leftAct, Inhomog.mul_ε, Inhomog.mul_ϖ, d.leibniz, smul_add, mul_smul,
    smul_inv_smul]
  abel

/-! ## What does not check -/

/-- Lemma 7.2 as printed is FALSE. Under the printed tilted map the augmented torsion
picks up an error term `−2 h⁻¹ (d_{A₀} h)`. -/
theorem torsion_mul_tauMinus (g : Inhomog H N) (h : H) :
    torsion d (g * tauMinus d h) = h⁻¹ • torsion d g - (d.c h + d.c h) := by
  simp only [torsion, tauMinus, Inhomog.mul_ε, Inhomog.mul_ϖ, d.leibniz, smul_sub]
  abel

/-- Lemma 6.5 as printed is FALSE in its first component, by the same error term. -/
theorem biConn_mul_tauMinus (g : Inhomog H N) (h : H) :
    biConn d (g * tauMinus d h) =
      (gaugeAct d (biConn d g).1 h - (d.c h + d.c h), gaugeAct d (biConn d g).2 h) := by
  ext
  · simp only [biConn, gaugeAct, tauMinus, Inhomog.mul_ϖ]
    abel
  · simp only [biConn, gaugeAct, tauMinus, Inhomog.mul_ε, d.leibniz]

/-- Lemma 7.2 is true for the opposite sign. -/
theorem torsion_mul_tauPlus (g : Inhomog H N) (h : H) :
    torsion d (g * tauPlus d h) = h⁻¹ • torsion d g := by
  simp only [torsion, tauPlus, Inhomog.mul_ε, Inhomog.mul_ϖ, d.leibniz, smul_sub]
  abel

/-- Lemma 6.5 is true for the opposite sign. -/
theorem biConn_mul_tauPlus (g : Inhomog H N) (h : H) :
    biConn d (g * tauPlus d h) = (gaugeAct d (biConn d g).1 h, gaugeAct d (biConn d g).2 h) := by
  ext
  · simp only [biConn, gaugeAct, tauPlus, Inhomog.mul_ϖ]
  · simp only [biConn, gaugeAct, tauPlus, Inhomog.mul_ε, d.leibniz]

/-- But for the opposite sign Lemma 6.3 is FALSE, by twice the same term. -/
theorem proj_mul_tauPlus (g : Inhomog H N) (h : H) :
    proj d (g * tauPlus d h) = proj d g + (g.ε * h) • (d.c h + d.c h) := by
  simp only [proj, tauPlus, Inhomog.mul_ε, Inhomog.mul_ϖ, d.leibniz, smul_add, mul_smul,
    smul_inv_smul]
  abel

/-- **No sign convention rescues Section 6–7 as printed.**

Fix either sign for the tilted map. If Lemma 6.3 (`π` is constant on tilted orbits) and
Lemma 7.2 (the augmented torsion is equivariant) both hold for that sign, then
`h⁻¹ (d_{A₀} h) = 0` for every gauge transformation `h`.

`N` is a real vector space in the draft, so the no-2-torsion hypothesis holds there. -/
theorem lemma63_and_lemma72_incompatible (h2 : ∀ n : N, n + n = 0 → n = 0)
    (hyp :
      ((∀ (g : Inhomog H N) (h : H), proj d (g * tauMinus d h) = proj d g) ∧
        (∀ (g : Inhomog H N) (h : H), torsion d (g * tauMinus d h) = h⁻¹ • torsion d g)) ∨
      ((∀ (g : Inhomog H N) (h : H), proj d (g * tauPlus d h) = proj d g) ∧
        (∀ (g : Inhomog H N) (h : H), torsion d (g * tauPlus d h) = h⁻¹ • torsion d g))) :
    ∀ h : H, d.c h = 0 := by
  intro h
  apply h2
  rcases hyp with ⟨-, hT⟩ | ⟨hπ, -⟩
  · have := hT 1 h
    rw [torsion_mul_tauMinus] at this
    exact neg_eq_zero.mp (by simpa [sub_eq_add_neg] using this)
  · have := hπ 1 h
    rw [proj_mul_tauPlus] at this
    have key : h • (d.c h + d.c h) = 0 := by simpa [smul_add] using this
    exact (smul_eq_zero_iff_eq h).mp key

/-! ## The repair the draft does not make

Keeping the opposite sign (so that the torsion is equivariant) and replacing eq. (6.11) by
`π'(ε, ϖ) = ε (ϖ − ε⁻¹ (d_{A₀} ε)) ε⁻¹` gives a consistent set of statements. So these
errors are fixable. They are recorded because a proof assistant will not accept the text
as written, which is the exercise. -/

/-- A corrected projection. -/
def projFixed (g : Inhomog H N) : N := g.ε • torsion d g

/-- CHECKED. The corrected projection is invariant under the opposite-sign tilted map. -/
theorem projFixed_mul_tauPlus (g : Inhomog H N) (h : H) :
    projFixed d (g * tauPlus d h) = projFixed d g := by
  rw [projFixed, torsion_mul_tauPlus]
  simp [projFixed, tauPlus, mul_smul]

end GU
