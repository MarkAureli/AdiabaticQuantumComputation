import Mathlib.Analysis.InnerProductSpace.PiL2
import AdiabaticQuantumComputation.Basic

/-!
# Diagonal Hamiltonians on N-qubit Hilbert Space

This file formalizes diagonal Hamiltonians on `QSpace N`, corresponding to Definition 1
(Phase Separator Hamiltonian) from arXiv:2302.04968.

## Main definitions

- `diagonalOp f`: the diagonal continuous linear map on `QSpace N` with eigenvalues
  `f : BitString N → ℂ`; maps `|z⟩ ↦ f(z) • |z⟩`.
- `objectiveHamiltonian f`: the objective Hamiltonian for `f : BitString N → ℝ`; this
  is the real-eigenvalue diagonal operator encoding the COP objective.
- `IsDiagonal H`: predicate asserting that `H` is diagonal in the computational basis.

## Main results

- `diagonalOp_apply`: pointwise action `(diagonalOp f v) z = f(z) * v(z)`.
- `diagonalOp_ket`: basis action `diagonalOp f (ket z) = f(z) • ket z`.
- `objectiveHamiltonian_ket`: basis action for the objective Hamiltonian.
- `diagonalOp_isDiagonal`, `objectiveHamiltonian_isDiagonal`: these operators are diagonal.
-/

/-! ## Diagonal operator -/

/-- The diagonal continuous linear map on `QSpace N` with complex eigenvalue function
`f : BitString N → ℂ`. Acts as `v ↦ (fun z => f(z) * v(z))` pointwise. -/
noncomputable def diagonalOp {N : ℕ} (f : BitString N → ℂ) : QSpace N →L[ℂ] QSpace N :=
  let e := EuclideanSpace.equiv (BitString N) ℂ
  e.symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun z => f z • ContinuousLinearMap.proj z) ∘L
    e.toContinuousLinearMap

/-- `diagonalOp f` acts pointwise: `(diagonalOp f v) z = f(z) * v(z)`. -/
theorem diagonalOp_apply {N : ℕ} (f : BitString N → ℂ)
    (v : QSpace N) (z : BitString N) :
    diagonalOp f v z = f z * v z := by
  simp [diagonalOp, ContinuousLinearEquiv.toContinuousLinearMap]

/-- `diagonalOp f` maps the computational basis vector `|z⟩` to `f(z) • |z⟩`. -/
theorem diagonalOp_ket {N : ℕ} (f : BitString N → ℂ) (z : BitString N) :
    diagonalOp f (ket z) = f z • ket z := by
  ext i
  simp only [diagonalOp_apply, ket, EuclideanSpace.single_apply, mul_ite, mul_one, mul_zero]
  simp [EuclideanSpace.single_apply]
  split_ifs with h
  · subst h; rfl
  · rfl

/-! ## Objective Hamiltonian -/

/-- The objective Hamiltonian for a COP with objective function `f : BitString N → ℝ`.
This is the diagonal operator with real eigenvalues `f(z)` at `|z⟩`, encoding the
objective value of each computational basis state. -/
noncomputable def objectiveHamiltonian {N : ℕ} (f : BitString N → ℝ) : QSpace N →L[ℂ] QSpace N :=
  diagonalOp (fun z => (f z : ℂ))

/-- `objectiveHamiltonian f` maps `|z⟩` to `↑(f z) • |z⟩`. -/
theorem objectiveHamiltonian_ket {N : ℕ} (f : BitString N → ℝ) (z : BitString N) :
    objectiveHamiltonian f (ket z) = (f z : ℂ) • ket z :=
  diagonalOp_ket _ z

/-! ## Diagonal predicate -/

/-- A continuous linear map `H : QSpace N →L[ℂ] QSpace N` is *diagonal in the computational
basis* if there exists `f : BitString N → ℂ` such that `H (ket z) = f(z) • ket z` for all
`z : BitString N`. -/
def IsDiagonal {N : ℕ} (H : QSpace N →L[ℂ] QSpace N) : Prop :=
  ∃ f : BitString N → ℂ, ∀ z : BitString N, H (ket z) = f z • ket z

/-- `diagonalOp f` is diagonal in the computational basis. -/
theorem diagonalOp_isDiagonal {N : ℕ} (f : BitString N → ℂ) :
    IsDiagonal (diagonalOp f) :=
  ⟨f, fun z => diagonalOp_ket f z⟩

/-- `objectiveHamiltonian f` is diagonal in the computational basis. -/
theorem objectiveHamiltonian_isDiagonal {N : ℕ} (f : BitString N → ℝ) :
    IsDiagonal (objectiveHamiltonian f) :=
  diagonalOp_isDiagonal _
