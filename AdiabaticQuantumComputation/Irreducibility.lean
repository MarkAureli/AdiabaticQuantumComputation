import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import AdiabaticQuantumComputation.Basic

/-!
# Irreducibility of Matrices (Definition 3)

This file formalizes the notion of irreducibility for matrices, following Definition 3
of arXiv:2302.04968.

## Main definitions

- `IsCoordIrreducible A`: a matrix `A : Matrix n n R` has no proper `A`-invariant
  coordinate subspace (the paper's Definition 3).

## Relationship to Mathlib

Mathlib's `Matrix.IsIrreducible` (in `Mathlib.LinearAlgebra.Matrix.Irreducible.Defs`)
is the Perron–Frobenius notion: it bundles component-wise non-negativity with strong
connectivity of the support graph. For non-negative matrices, strong connectivity is
equivalent to coordinate-irreducibility.

`Matrix.IsIrreducible.isCoordIrreducible` states this implication (currently sorry'd).

## Main results

- `IsCoordIrreducible`: Definition 3 of the paper.
- `Matrix.IsIrreducible.isCoordIrreducible`: Mathlib's P-F irreducibility implies ours.
-/

/-! ## Coordinate-irreducibility (Definition 3) -/

/-- A matrix `A : Matrix n n R` is *coordinate-irreducible* (Definition 3 of arXiv:2302.04968)
if it has no proper `A`-invariant coordinate subspace.

A subset `S ⊆ n` defines the *coordinate subspace* `span {e_j | j ∈ S}`. This subspace is
`A`-invariant iff `A i j = 0` whenever `i ∉ S` and `j ∈ S` (no "leaking" out of `S`).
Irreducibility means no proper nonempty `S` is `A`-invariant:
for every proper nonempty `S`, there is an edge `j → i` with `j ∈ S`, `i ∉ S`. -/
def IsCoordIrreducible {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [Ring R]
    (A : Matrix n n R) : Prop :=
  ∀ S : Finset n, S.Nonempty → S ≠ Finset.univ →
    ∃ i ∉ S, ∃ j ∈ S, A i j ≠ 0

/-! ## Connection to Mathlib's Perron–Frobenius irreducibility -/

/-- For a non-negative irreducible matrix (in the Perron–Frobenius sense of Mathlib),
the coordinate-irreducibility condition holds.

*Proof sketch*: `Matrix.IsIrreducible` requires `Quiver.IsSStronglyConnected n`, meaning
every node `i` can reach every node `j` via a directed path in the support graph of `A`.
In particular, for any proper nonempty `S`, there exists an edge from some `j ∈ S` to
some `i ∉ S`, witnessing `A i j > 0`. -/
lemma Matrix.IsIrreducible.isCoordIrreducible
    {n : Type*} [Fintype n] [DecidableEq n] [Nontrivial n]
    {A : Matrix n n ℝ} (hA : A.IsIrreducible) :
    IsCoordIrreducible A := by
  sorry
