import Mathlib.Analysis.InnerProductSpace.PiL2
import AdiabaticQuantumComputation.Basic
import AdiabaticQuantumComputation.DiagonalHamiltonian
import AdiabaticQuantumComputation.Irreducibility

/-!
# QAA Phase 2 Definitions

This file formalizes the core definitions of the Quantum Adiabatic Algorithm (QAA)
framework from arXiv:2302.04968:

- **Definition 1 (Phase Separator):** a diagonal Hamiltonian whose restriction to the
  feasible set has the optimal solution space as its top eigenspace.
- **Definition 5 (Mixer Hamiltonian):** a Hamiltonian that preserves feasibility, is
  component-wise non-negative on the feasible set, and is irreducible there.
- **Linear interpolation `H(t)`:** the time-dependent Hamiltonian `(1 - t)B + tC` used
  in the quasi-adiabatic evolution of Theorem 7.

## Main definitions

- `restrictionMatrix B S`: real matrix of `B` restricted to basis states in `S`, with
  entries `⟨ket i | B | ket j⟩.re`.
- `IsPhaseSeparator H S Sopt`: Definition 1.
- `IsMixerHamiltonian B S`: Definition 5.
- `linearInterp B C t`: the linear interpolation Hamiltonian.

## Main results

- `linearInterp_zero`, `linearInterp_one`: boundary values of the interpolation.
-/

/-! ## Restriction matrix -/

/-- The real matrix of a Hamiltonian `B` restricted to the feasible basis states `S`.
Entry `(i, j)` is the real part of `⟨ket i | B | ket j⟩ = inner ℂ (ket i) (B (ket j))`.

Under the mixer conditions (Definition 5), the imaginary parts of all entries vanish,
so this matrix fully captures the structure of `B|_S`. It is used to state the
irreducibility and non-negativity conditions. -/
noncomputable def restrictionMatrix {N : ℕ} (B : QSpace N →L[ℂ] QSpace N)
    (S : Finset (BitString N)) :
    Matrix {z : BitString N // z ∈ S} {z : BitString N // z ∈ S} ℝ :=
  fun i j => (inner ℂ (ket i.1) (B (ket j.1))).re

/-! ## Definition 1: Phase Separator Hamiltonian -/

/-- **Definition 1 (Phase Separator Hamiltonian)** (arXiv:2302.04968).

A Hamiltonian `H` is a *phase separator* for the combinatorial optimisation problem
with feasible set `S ⊆ BitString N` and optimal solution set `Sopt` if:
1. `H` is diagonal in the computational basis (`IsDiagonal H`), and
2. `Sopt` is exactly the set of maximisers of the eigenvalue function of `H` on `S`:
   a basis state `z` belongs to `Sopt` iff `z ∈ S` and `f(z) ≥ f(w)` for all `w ∈ S`,
   where `H(|z⟩) = f(z) |z⟩`. -/
def IsPhaseSeparator {N : ℕ} (H : QSpace N →L[ℂ] QSpace N)
    (S Sopt : Finset (BitString N)) : Prop :=
  IsDiagonal H ∧
  ∃ f : BitString N → ℝ,
    (∀ z, H (ket z) = (f z : ℂ) • ket z) ∧
    (∀ z, z ∈ Sopt ↔ z ∈ S ∧ ∀ w ∈ S, f w ≤ f z)

/-! ## Definition 5: Mixer Hamiltonian -/

/-- **Definition 5 (Mixer Hamiltonian)** (arXiv:2302.04968).

A Hamiltonian `B` is a *mixer* for the combinatorial optimisation problem with feasible
set `S ⊆ BitString N` if:
1. **Feasibility preservation:** `B` maps the coordinate subspace `span{|z⟩ | z ∈ S}`
   into itself, i.e., `⟨ket w | B | ket z⟩ = 0` for all `z ∈ S` and `w ∉ S`.
2. **Component-wise non-negativity:** all matrix entries `⟨ket i | B | ket j⟩` for
   `i j ∈ S` are non-negative real numbers (zero imaginary part, non-negative real part).
3. **Irreducibility:** the restriction matrix `B|_S` is coordinate-irreducible
   (`IsCoordIrreducible`). -/
def IsMixerHamiltonian {N : ℕ} (B : QSpace N →L[ℂ] QSpace N)
    (S : Finset (BitString N)) : Prop :=
  -- (1) feasibility preservation: B maps span{|z⟩ | z ∈ S} into itself
  (∀ z ∈ S, ∀ w : BitString N, w ∉ S → inner ℂ (ket w) (B (ket z)) = 0) ∧
  -- (2) component-wise non-negative and real on S
  (∀ i j : {z : BitString N // z ∈ S},
    (inner ℂ (ket i.1) (B (ket j.1))).im = 0 ∧
    0 ≤ (inner ℂ (ket i.1) (B (ket j.1))).re) ∧
  -- (3) B|_S is coordinate-irreducible
  IsCoordIrreducible (restrictionMatrix B S)

/-! ## Linear interpolation -/

/-- The linear interpolation `H(t) := (1 - t) · B + t · C` between Hamiltonians `B`
and `C`, parametrised by `t : ℝ`. At `t = 0` we recover the mixer `B`; at `t = 1`
we recover the phase separator `C`. This is the time-dependent Hamiltonian of the
quasi-adiabatic evolution in Theorem 7. -/
noncomputable def linearInterp {N : ℕ}
    (B C : QSpace N →L[ℂ] QSpace N) (t : ℝ) : QSpace N →L[ℂ] QSpace N :=
  (1 - (t : ℂ)) • B + (t : ℂ) • C

/-- At `t = 0`, the linear interpolation equals the mixer `B`. -/
@[simp]
theorem linearInterp_zero {N : ℕ} (B C : QSpace N →L[ℂ] QSpace N) :
    linearInterp B C 0 = B := by
  simp [linearInterp]

/-- At `t = 1`, the linear interpolation equals the phase separator `C`. -/
@[simp]
theorem linearInterp_one {N : ℕ} (B C : QSpace N →L[ℂ] QSpace N) :
    linearInterp B C 1 = C := by
  simp [linearInterp]
