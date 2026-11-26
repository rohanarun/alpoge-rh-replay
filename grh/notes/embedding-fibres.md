# Pairing complex embeddings over infinite places

This note explains the change of index in
[`New.Variety.prod_embeddings_eq_prod_pairs`](../src/Lib/General/NumberTheory/EmbeddingsAndDifferent.lean#L254-L263).
It is about the readable edition and does not use a new number-theoretic hypothesis.

## Why there are two factors per place

Let `E` be a totally complex number field. The map from complex embeddings
of (E) to infinite places is `InfinitePlace.mk`. A `PlaceEmbedding E`
chooses an embedding `Φ v` over each place `v`. In Lean, `mk_Φ` identifies
its place, and conjugating an embedding does not change its place. The two
embeddings are distinct: an embedding fixed by conjugation would be real,
which is excluded by total complexity (`conjugate_ne_self`).

Conversely, if `mk σ = v`, apply `mk_eq_iff` to `Φ v` and `σ`. It says
that `σ` is the chosen embedding or its conjugate. Thus the fibre over
`v` contains exactly those two distinct embeddings. The proof first uses
`prod_fiberwise` to group by place, then evaluates the product over each
two-element fibre. No order of embeddings is needed, and the factor
function can take values in any commutative monoid. The same change of
index gives the additive sum statement through `to_additive`.

## Where the regrouping pays off

- **Norm of an algebraic Hecke character.** In
  [`norm_padic_eq_prod`](../src/Lib/ClassField/HeckeCharacter/AlgebraicValues.lean#L380-L398),
  the norm formula initially runs over embeddings. Pairing them places the
  two opposite exponents at one infinite place. The proof then identifies
  the finite-idele values through the conjugate primes; regrouping alone
  does not assert that the two values are equal.
- **Type of the determinant character.** In
  [`AttachedRepresentations.lean`](../src/Lib/GaloisRep/Main/AttachedRepresentations.lean#L407-L412),
  the definition of `m σ` gives opposite signs according to whether
  `σ` is the chosen embedding. Grouping by place turns the two terms
  into the powers of a ratio used in the principal-idele formula.
- **Weyl character comparison.** In
  [`WeightOccurs.lean`](../src/Lib/Shimura/Transfer/WeightOccurs.lean#L425-L435),
  the determinant and root expressions begin as products over
  embeddings, whereas the Weyl formula is already written by place.
  Pairing converts them to the same index set before the proof compares
  the factors place by place.

These uses share the same finite-index change, but the work after it is
different: each proof supplies its own relation between the two conjugate
factors. Keeping that distinction is useful when tracing the proof or
when changing the implementation of the pairing lemma.
