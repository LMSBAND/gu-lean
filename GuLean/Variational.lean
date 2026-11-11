import Mathlib

/-!
# The index lemma behind the action obstruction

Write the shiab operator through its pairing
`K a b c X Y = ⟨e^c ⊗ Y, ∗ ⊙ (e^a ∧ e^b ⊗ X)⟩`, so `K` is antisymmetric in `a b`.

The draft's eq. (9.7) says the field equation `⊙ F_A + κ ∗T` is the derivative of an action
in the direction of the connection. That requires the linearisation `β ↦ ⊙ (d_B β + [T ∧ β])`
to be self-adjoint for every `T`. After an integration by parts the part without `T` reads

  `K a c b Y X = -K a b c X Y`   (`h2` below),

and the part linear in `T` reads

  `K a b c [Z, X] Y = K a c b [Z, Y] X`   (`h3` below).

The theorems here show that these force `K a b c` to be, for each `a b c`, a symmetric
bilinear form that is totally antisymmetric in its indices and invariant under the bracket
with every `Z`. The paper combines this with two standard facts that are not formalised here:
the invariant symmetric forms on `u(64,64)` are spanned by `Tr(XY)` and `Tr(X)Tr(Y)`, and
`Spin(7,7)` fixes no nonzero 3-form.
-/

namespace GU.Variational

variable {ι A R : Type*} [AddCommGroup R]

/-- The first-order condition makes the pairing symmetric in its two algebra arguments. -/
theorem symm_of_firstOrder (K : ι → ι → ι → A → A → R)
    (h1 : ∀ a b c X Y, K b a c X Y = -K a b c X Y)
    (h2 : ∀ a b c X Y, K a c b Y X = -K a b c X Y) :
    ∀ a b c X Y, K a b c Y X = K a b c X Y := by
  intro a b c X Y
  rw [h2 a c b X Y, h1 c a b X Y, h2 c b a Y X, h1 b c a Y X, h2 b a c X Y, h1 a b c X Y]
  simp

/-- ... and antisymmetric in its last two indices, hence totally antisymmetric. -/
theorem antisymm_of_firstOrder (K : ι → ι → ι → A → A → R)
    (h1 : ∀ a b c X Y, K b a c X Y = -K a b c X Y)
    (h2 : ∀ a b c X Y, K a c b Y X = -K a b c X Y) :
    ∀ a b c X Y, K a c b X Y = -K a b c X Y := by
  intro a b c X Y
  rw [← symm_of_firstOrder K h1 h2 a c b X Y]
  exact h2 a b c X Y

/-- With the second-order condition, each `K a b c` is invariant under the bracket with every
element of the algebra. -/
theorem adInvariant_of_secondOrder (br : A → A → A) (K : ι → ι → ι → A → A → R)
    (h1 : ∀ a b c X Y, K b a c X Y = -K a b c X Y)
    (h2 : ∀ a b c X Y, K a c b Y X = -K a b c X Y)
    (h3 : ∀ a b c X Y Z, K a b c (br Z X) Y = K a c b (br Z Y) X) :
    ∀ a b c X Y Z, K a b c (br Z X) Y + K a b c X (br Z Y) = 0 := by
  intro a b c X Y Z
  rw [h3 a b c X Y Z, antisymm_of_firstOrder K h1 h2 a b c (br Z Y) X,
    symm_of_firstOrder K h1 h2 a b c X (br Z Y)]
  simp

end GU.Variational
