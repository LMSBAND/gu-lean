# Geometric Unity, as far as Lean will take it

A Lean 4 / Mathlib formalization of the parts of Eric Weinstein's *Geometric Unity:
Author's Working Draft v1.0* (April 1st 2021) that are written down precisely enough to
formalize, and a record of where it stops.

The paper is `paper/gu-lean.pdf`.

Build: `lake exe cache get && lake build`. Nothing uses `sorry`; `GuLean/Audit.lean`
prints the axioms each result depends on.

## Result

| Draft | Statement | Status | Lean |
|---|---|---|---|
| §3.1, eq. 3.8–3.9 | Signature of the Frobenius form on the fibre of metrics | True: (7,3) as defined, (4,6) after the sign flip the draft declares | `Signature.frob_self`, `frob_trace_direction` |
| §3.5 | The signature totals leading to (7,7) | True | `Signature.section_3_5_sums` |
| §3.5, eq. 3.21–3.27 | Which Clifford degrees form gl(64,ℝ), so(64,64), u(64,64) | Closed under bracket, dimensions right, given the standard degree rule | `CliffordGrading.lean` |
| §4, eq. 4.2–4.3 | Internal spinor dimensions 32 and 16 | True | `Signature.eq_4_3` |
| §8 | Dimension counts (2¹⁴ = 128², the Λⁱ split of u(64,64)) | True | `Dimensions.lean` |
| Def. 5.1, eq. 5.9 | The inhomogeneous gauge group is a group | True | `Inhomog.instGroup` |
| eq. 6.2 | Right action of G on connections | True | `connAct_mul` |
| Lemma 6.1 | The tilted map τ is a homomorphism | True | `tauMinus_mul` |
| §6.2 | "Flipped" map τ̂ parameterizes the stabilizer of A₀ | True, but τ̂ is the same formula as τ | `tauMinus_eq_tauHat` |
| Lemma 6.3 | π is constant on tilted orbits | True for τ as printed | `proj_mul_tauMinus` |
| Lemma 6.4 | Left action of G on N | True | `leftAct_mul` |
| Lemma 6.5 | The bi-connection map is equivariant | **False as printed** | `biConn_mul_tauMinus` |
| Lemma 7.2 | The augmented torsion is equivariant | **False as printed** | `torsion_mul_tauMinus` |
| §§6–7 together | Lemmas 6.3 and 7.2 for one sign of τ | **Inconsistent** | `lemma63_and_lemma72_incompatible` |
| §§6–7, three signs changed | Every lemma of Sections 6–7 | True | `Repaired.lean` |
| Def. 8.1 | The forms Φᵢ | **Not determined**, even up to scale | `equivariant_mul_commuting` |
| eq. 8.1 | The conjugation recipe is equivariant for every Φ | True | `conjugated_pairing_equivariant` |
| eq. 9.3 | The sample operator is Einstein's contraction | One reading of eight (numerical) | `experiments/einstein_check.py` |
| §8, eq. 9.2 | The shiab operator | **Not defined** | `FieldEquationInputs.shiab` |
| eq. 9.8 | The field equation is gauge covariant | Only as an implication from an undefined operator's assumed properties | `upsilon_equivariant` |
| Def. 8.1 | Dimension of each space the Φᵢ are drawn from | Exactly 2 (computed) | `experiments/count_operators.py` |
| eq. 9.2 | Number of independent operators of the stated kind | 200 (computed) | `experiments/count_operators.py` |
| §8.2, eq. 12.6 | The operator annihilates the Weyl curvature | True for all 200 (computed) | `experiments/count_operators.py` |
| eq. 9.4, 9.7 | Eq. 9.8 is the Euler–Lagrange equation of the action | **False for every nonzero operator** | `Variational.lean`, `experiments/count_variational.py` |

Everything before Section 6 that could be checked is correct. It is also standard: these
are known facts about symmetric matrices and Clifford algebras. The errors begin where the
draft's own constructions begin, and the definitions run out at the one new operator the
field equation needs.

## The sign error

The draft defines the tilted map as τ(h) = (h, −h⁻¹ d h) in eq. (6.4). Lemma 7.2, the
equivariance of the augmented torsion, is then off by −2 h⁻¹ d h. The printed proof
changes the sign of that term between its first and second lines (eq. 7.4), and the same
happens in eq. (6.20). Flipping the sign of τ makes Lemmas 6.5 and 7.2 true and makes
Lemma 6.3 false by the same amount. `lemma63_and_lemma72_incompatible` proves that no
choice of sign makes both hold unless every gauge transformation is covariantly constant.

The draft's footnote 7 says there "may be 2 or more conflicting conventions in this
section". There are, and this is where. The error is repairable: `projFixed` gives a
corrected projection for which everything is consistent. The draft does not make the
repair.

## The shiab operator

The field equation (9.8) is ⊙F = −κ₁ ∗T. The operator ⊙ is the one thing in it that is
new, and the draft does not define it. Section 8 offers what one "might look like", says
the author "is no longer in a position to go chasing after the complete picture", and
reports that he "has been unable to locate the notes from decades ago that originally
picked out the operator of choice".

The candidate that is written down, eq. (9.3), is built from forms Φ₁ and Φ₂. Definition
8.1 says only that the Φᵢ are "a basis for the invariant subspaces" of
[Λⁱ(ℝ^{7,7}) ⊗ u(64,64)]^{Spin(7,7)}. Those subspaces are not one-dimensional. Given any
invariant Φ, multiplying by the Clifford volume element gives another
(`equivariant_mul_commuting`), and for Φ₁ the two live in degrees 1 and 13, both of which
the draft's eq. (8.5) places inside u(64,64). So even the sample operator has free
parameters the draft does not fix. (The equivariance step is machine-checked; the two
facts about Cl(7,7) it is applied to are standard and are not formalized here.)

In Lean the operator can therefore only be a free parameter. `upsilon_equivariant` is
what remains of the theory's central claim: the field equation is gauge covariant *if*
someone supplies an operator with the right equivariance property.

## Filling the gap from the literature

With the textbook tautological Clifford forms for Φ₁ and Φ₂, the sample operator (9.3)
applied to the spin curvature of a metric annihilates the Weyl part in every reading. Read
as printed, with commutators, its scalar term vanishes and it is the Ricci tensor alone.
With a commutator in the first term and the draft's symmetric product in both brackets of
the second, it is the Einstein tensor with the printed coefficient ½. This is a numerical
check in dimensions 4 and 6 with a positive-definite metric: `python3
experiments/einstein_check.py`. It covers so(7,7), 91 of the 16384 dimensions of u(64,64).

## Counting the operators

The operators the draft describes are, before conjugation by ε, the Spin(7,7)-equivariant
linear maps Λ² ⊗ u(64,64) → Λ¹³ ⊗ u(64,64). There are exactly 200 independent ones
(`python3 experiments/count_operators.py`, a Brauer–Klimyk computation run in two orders that
agree). Every one of them annihilates the Weyl curvature, so that property selects nothing.
On the curvature of a metric they produce only traceless Ricci and scalar terms, in Clifford
degrees 1 and 13: four parameters, which Einstein's equation constrains. The other 196 are
not constrained by anything in the draft.

## The action does not give the equation

The draft's eq. (9.7) says the field equation (9.8) is the derivative of the action (9.4) in
the direction of the connection. For that to hold, the linearised equation must be
self-adjoint. `GuLean/Variational.lean` proves that this forces the operator's pairing to be
a totally antisymmetric three-index family of symmetric forms on u(64,64), each invariant
under the whole Lie algebra. Such forms are multiples of the trace forms, so the operator
would have to be built from a Spin(7,7)-invariant three-form, and there is none. Of the 200
operators, 48 pass the first-order condition and none passes both
(`python3 experiments/count_variational.py`). In dimension 4 a brute-force construction of
every operator as a matrix gives 40, 8 and 0 (`python3 experiments/brute_force_d4.py`).

Status: the index lemma is machine-checked; the two facts about invariant forms are standard
and not formalized; the derivation of the two conditions from eq. (9.7) is by hand and has not
been reviewed.

## Not attempted

The bundle-level constructions (the observerse as a manifold, the chimeric bundle, spinor
bundles, curvature, the Hodge star) are standard differential geometry that Mathlib cannot
yet express: it has no spin structures or connections on associated bundles. Those are
gaps in Mathlib, not in the draft, and are not counted against it. The Clifford degree rule
used in `CliffordGrading.lean` and the isomorphism Cl(7,7) ≅ ℝ(128) are taken as known
rather than derived. Sections 10–12 depend on the undefined operator.

## Sources

- E. Weinstein, *Geometric Unity: Author's Working Draft, v 1.0*, April 1st 2021.
- T. Nguyen and T. Polya, *A Response to Geometric Unity*, February 23, 2021.
