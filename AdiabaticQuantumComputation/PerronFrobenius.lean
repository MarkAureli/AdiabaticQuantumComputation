import AdiabaticQuantumComputation.Irreducibility

/-!
# Perron–Frobenius Theorem (Theorem 4)

This file states Theorem 4 (Perron–Frobenius) of arXiv:2302.04968 as a sorry'd axiom.
The theorem is a classical result in the theory of non-negative matrices; formalizing
it in Lean from scratch is out of scope. It is used as a black-box ingredient in the
proof of Theorem 7.

## Main results

- `perronFrobenius`: a component-wise non-negative coordinate-irreducible matrix has a
  unique largest real eigenvalue (the Perron root) `ρ > 0`, whose eigenspace is
  one-dimensional and spanned by an all-positive vector.
-/

/-! ## Theorem 4 (Perron–Frobenius) -/

/-- **Theorem 4 (Perron–Frobenius).** Let `n` be a nontrivial finite index type and
`A : Matrix n n ℝ` be component-wise non-negative and coordinate-irreducible. Then:
- there exists a *Perron root* `ρ > 0` and a *Perron vector* `v : n → ℝ` with all
  strictly positive components satisfying the eigenvalue equation `A.mulVec v = ρ • v`;
- `ρ` is the largest real eigenvalue: for every non-zero real eigenvector `w` for
  eigenvalue `λ`, we have `λ ≤ ρ`;
- the `ρ`-eigenspace is one-dimensional: every eigenvector for `ρ` is a scalar multiple
  of `v`.

This is the classical Perron–Frobenius theorem for irreducible non-negative matrices;
see e.g. Horn–Johnson, *Matrix Analysis*, Chapter 8. -/
theorem perronFrobenius {n : Type*} [Fintype n] [DecidableEq n] [Nontrivial n]
    {A : Matrix n n ℝ} (hnn : ∀ i j, 0 ≤ A i j) (hirr : IsCoordIrreducible A) :
    ∃ ρ : ℝ, ∃ v : n → ℝ,
      0 < ρ ∧
      (∀ i, 0 < v i) ∧
      A.mulVec v = ρ • v ∧
      (∀ μ : ℝ, (∃ w : n → ℝ, w ≠ 0 ∧ A.mulVec w = μ • w) → μ ≤ ρ) ∧
      (∀ w : n → ℝ, A.mulVec w = ρ • w → ∃ c : ℝ, w = c • v) := by
  sorry
