import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Foundations for Adiabatic Quantum Computation

Basic objects for the formalization of arXiv:2302.04968
("Elementary Proof of QAOA Convergence").

## Main definitions

- `BitString N`: bit strings of length N, i.e. `Fin (2^N)`.
- `QSpace N`: the N-qubit Hilbert space `ℂ^(2^N)` as an `EuclideanSpace`.
- `ket z`: the computational basis vector `|z⟩` for `z : BitString N`.

## Main results

- `orthonormal_ket`: the `ket` vectors form an orthonormal family.
- `ket_norm`: each `ket` vector has unit norm.
- `ket_inner`: `⟪ket z, ket w⟫_ℂ = if z = w then 1 else 0`.
-/

/-! ## Bit strings -/

/-- A bit string of length `N` is an element of `Fin (2^N)`.
We index the `2^N` computational basis states by `{0, …, 2^N - 1}`. -/
abbrev BitString (N : ℕ) : Type := Fin (2 ^ N)

/-! ## N-qubit Hilbert space -/

/-- The N-qubit Hilbert space `ℂ^(2^N)`, realized as `EuclideanSpace ℂ (Fin (2^N))`. -/
abbrev QSpace (N : ℕ) : Type := EuclideanSpace ℂ (BitString N)

/-! ## Computational basis -/

/-- The computational basis vector `|z⟩` for `z : BitString N`. -/
noncomputable def ket {N : ℕ} (z : BitString N) : QSpace N :=
  EuclideanSpace.single z 1

/-- The `ket` vectors form an orthonormal family. -/
theorem orthonormal_ket (N : ℕ) : Orthonormal ℂ (ket (N := N)) :=
  EuclideanSpace.orthonormal_single

/-- Each `ket` vector has unit norm. -/
theorem ket_norm {N : ℕ} (z : BitString N) : ‖ket z‖ = 1 :=
  (orthonormal_ket N).1 z

/-- `inner ℂ (ket z) (ket w) = 1` if `z = w`, and `0` otherwise. -/
theorem ket_inner {N : ℕ} (z w : BitString N) :
    inner ℂ (ket z) (ket w) = if z = w then (1 : ℂ) else 0 := by
  simp only [ket, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply,
             map_one, one_mul]
