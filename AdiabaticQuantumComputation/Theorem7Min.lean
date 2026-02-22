import AdiabaticQuantumComputation.QAADefinitions
import AdiabaticQuantumComputation.PerronFrobenius
import AdiabaticQuantumComputation.Theorem7

/-!
# Theorem 7 — Minimization Analogue

This file extends Theorem 7 of arXiv:2302.04968 to **minimization** problems.

## Setting

In the original Theorem 7, the phase separator `C` encodes a *maximization* COP
and the mixer `B` has component-wise **non-negative** entries on the feasible set `S`.
The Perron–Frobenius theorem guarantees that the **largest** eigenvalue of the
interpolated Hamiltonian `H(t)|_S = (1-t)B|_S + tC|_S` is non-degenerate for `t ∈ [0,1)`,
and the quasi-adiabatic evolution starting from a highest energy state of `B|_S` converges
to the maximization optimal subspace.

Here we prove the symmetric statement for minimization: we start from a **lowest** energy
state of `B|_S` and converge to the **minimization** optimal subspace (argmin of `f` on `S`).

## Key Mathematical Argument

The obstruction: Perron–Frobenius only guarantees non-degeneracy of the **largest**
eigenvalue of non-negative irreducible matrices, not the smallest.

The fix: define a *minimization mixer* as a Hamiltonian `B` whose restriction `B|_S` has
**non-positive** entries (i.e., `−B|_S` is a non-negative matrix) and `−B|_S` is
coordinate-irreducible. Then for `t ∈ [0, 1)`:

```
−(H(t)|_S) = (1−t)(−B|_S) + t(−C|_S)
```

is non-negative + irreducible by Corollary 6 (`−B|_S` is non-negative irreducible;
`−C|_S` is diagonal). Perron–Frobenius then gives a non-degenerate **largest** eigenvalue
of `−(H(t)|_S)`, which is precisely the **smallest** eigenvalue of `H(t)|_S`. The rest of
the proof (Kato analytic perturbation theory + adiabatic theorem) is structurally identical
to the maximization case.

## Main definitions

- `IsMinPhaseSeparator C S Sopt`: `C` is a phase separator for a minimization COP
  (diagonal; `Sopt = argmin f` on `S`).
- `IsMinMixerHamiltonian B S`: `B` is a minimization mixer (feasibility preservation;
  component-wise non-positive on `S`; `−B|_S` is coordinate-irreducible).
- `IsBottomEnergyState B S ι`: `ι` is a lowest energy eigenstate of `B|_S`.

## Main results

- `katoSpectralProjectionMin`: Kato's analytic perturbation lemma for the minimization
  case (sorry'd).
- `theorem7Min`: Theorem 7 for minimization, proved modulo `katoSpectralProjectionMin`.
-/

/-! ## Definition 1 (minimization): Phase Separator Hamiltonian -/

/-- **Minimization Phase Separator (Definition 1, minimization variant).**

A Hamiltonian `H` is a *minimization phase separator* for the COP with feasible set `S`
and optimal solution set `Sopt` if:
1. `H` is diagonal in the computational basis (`IsDiagonal H`), and
2. `Sopt` is exactly the set of **minimisers** of the eigenvalue function `f` of `H` on `S`:
   `z ∈ Sopt ↔ z ∈ S ∧ ∀ w ∈ S, f z ≤ f w`. -/
def IsMinPhaseSeparator {N : ℕ} (H : QSpace N →L[ℂ] QSpace N)
    (S Sopt : Finset (BitString N)) : Prop :=
  IsDiagonal H ∧
  ∃ f : BitString N → ℝ,
    (∀ z, H (ket z) = (f z : ℂ) • ket z) ∧
    (∀ z, z ∈ Sopt ↔ z ∈ S ∧ ∀ w ∈ S, f z ≤ f w)

/-! ## Definition 5 (minimization): Mixer Hamiltonian -/

/-- **Minimization Mixer Hamiltonian (Definition 5, minimization variant).**

A Hamiltonian `B` is a *minimization mixer* for the COP with feasible set `S` if:
1. **Feasibility preservation:** `B` maps `span{|z⟩ | z ∈ S}` into itself,
   i.e., `⟨ket w | B | ket z⟩ = 0` for all `z ∈ S` and `w ∉ S`.
2. **Component-wise non-positive on `S`:** all matrix entries `⟨i|B|j⟩` for `i j ∈ S`
   are non-positive real numbers (zero imaginary part, non-positive real part).
3. **Irreducibility of `−B|_S`:** the negated restriction matrix `−restrictionMatrix B S`
   is coordinate-irreducible.

**Why this works:** condition (2) ensures `−B|_S` is non-negative, and combined with
condition (3) it satisfies the hypotheses of Perron–Frobenius applied to `−H(t)|_S`. -/
def IsMinMixerHamiltonian {N : ℕ} (B : QSpace N →L[ℂ] QSpace N)
    (S : Finset (BitString N)) : Prop :=
  -- (1) feasibility preservation
  (∀ z ∈ S, ∀ w : BitString N, w ∉ S → inner ℂ (ket w) (B (ket z)) = 0) ∧
  -- (2) component-wise non-positive and real on S
  (∀ i j : {z : BitString N // z ∈ S},
    (inner ℂ (ket i.1) (B (ket j.1))).im = 0 ∧
    (inner ℂ (ket i.1) (B (ket j.1))).re ≤ 0) ∧
  -- (3) −B|_S is coordinate-irreducible
  IsCoordIrreducible (-(restrictionMatrix B S))

/-! ## Lowest energy state -/

/-- `ι` is a *lowest energy state* of `B|_S`: `ι` is a nonzero vector in
`span{|z⟩ | z ∈ S}`, an eigenvector of `B` for eigenvalue `μ ∈ ℝ`, and `μ` is the
**smallest** eigenvalue of `B` on the feasible subspace. -/
def IsBottomEnergyState {N : ℕ} (B : QSpace N →L[ℂ] QSpace N)
    (S : Finset (BitString N)) (ι : QSpace N) : Prop :=
  ι ≠ 0 ∧
  ι ∈ Submodule.span ℂ (ket '' (S : Set (BitString N))) ∧
  ∃ μ : ℝ, B ι = (μ : ℂ) • ι ∧
    ∀ ν : ℝ, (∃ w : QSpace N, w ≠ 0 ∧
               w ∈ Submodule.span ℂ (ket '' (S : Set (BitString N))) ∧
               B w = (ν : ℂ) • w) → μ ≤ ν

/-! ## Kato Analytic Perturbation Theory (minimization) -/

/-- **Kato's Analytic Perturbation Theory — minimization variant.**

For the linearly interpolated Hamiltonian `H(t) = (1-t)B + tC` with `B` a minimization
mixer and `C` a minimization phase separator, there exists a C²-family of spectral
projections `P(t)` onto the **bottom** eigenspace of `H(t)|_S`, valid on all of `[0,1]`:

- **Existence:** The bottom eigenvalue of `H(t)|_S` is non-degenerate for all `t ∈ [0,1)`
  by Perron–Frobenius applied to `−H(t)|_S`:
  ```
  −(H(t)|_S) = (1−t)(−B|_S) + t(−C|_S)
  ```
  Here `−B|_S` is non-negative and coordinate-irreducible (by `hB.2`), and `−C|_S` is
  diagonal (since `C` is diagonal). By Corollary 6, `−(H(t)|_S)` is non-negative
  irreducible for `t ∈ [0,1)`. Perron–Frobenius gives a non-degenerate largest eigenvalue
  of `−(H(t)|_S)`, which is the smallest eigenvalue of `H(t)|_S`.
  Kato's theorem extends the spectral projection analytically to `t = 1`.
- **Projection property:** `P(t)² = P(t)` for all `t`.
- **Spectral property:** `H(t) ∘ P(t) = μ(t) · P(t)` for the bottom eigenvalue `μ(t)`.
- **Initial condition:** `|ι⟩ ∈ ran P(0)` (since `ι` is the Perron eigenvector of `−B|_S`,
  hence the bottom energy state of `B|_S`).
- **Final range:** `ran P(1) = optimalSubspace Sopt`.

*Reference:* Kato, *Perturbation Theory for Linear Operators* (1966), Thm II.6.1. -/
theorem katoSpectralProjectionMin {N : ℕ}
    (B C : QSpace N →L[ℂ] QSpace N)
    (S Sopt : Finset (BitString N))
    (hB : IsMinMixerHamiltonian B S)
    (hC : IsMinPhaseSeparator C S Sopt)
    (ι : QSpace N)
    (hι : IsBottomEnergyState B S ι) :
    ∃ P : ℝ → QSpace N →L[ℂ] QSpace N,
      (∀ t, P t ∘L P t = P t) ∧
      (∀ t, ∃ μ : ℝ, linearInterp B C t ∘L P t = (μ : ℂ) • P t) ∧
      P 0 ι = ι ∧
      (∀ φ : QSpace N, P 1 φ = φ ↔ φ ∈ optimalSubspace Sopt) := by
  sorry

/-! ## Theorem 7 (minimization) -/

/-- **Theorem 7 — Minimization Analogue** (Phase 4, arXiv:2302.04968 extension).

Consider a minimization COP with feasible set `S ⊆ BitString N`, optimal solution set
`Sopt ⊆ S` (the argmin states), minimization phase separator `C`, and minimization mixer
`B`. If `|ι⟩ ∈ S` is a **lowest** energy state of `B|_S`, then the final state
`U_T(1)|ι⟩` of the quasi-adiabatic evolution w.r.t. `H(t) = (1-t)B + tC` converges to
the optimal subspace as `T → ∞`:

for every `ε > 0` there exists `T₀` such that for all `T ≥ T₀` there is a state
`φ ∈ optimalSubspace Sopt` with `‖U_T(1)|ι⟩ − φ‖ < ε`.

**Proof:** Structurally identical to Theorem 7 (maximization):
1. `katoSpectralProjectionMin` gives a spectral projection family `P` tracking the bottom
   eigenspace, with `ran P(0) ∋ ι` and `ran P(1) = Sopt`.
2. `adiabaticTheorem` gives `‖U_T(1)|ι⟩ − P(1)(U_T(1)|ι⟩)‖ → 0` as `T → ∞`.
3. The witness `φ := P(1)(U_T(1)|ι⟩)` lies in `optimalSubspace Sopt` since `P(1)` is a
   projection and `ran P(1) = optimalSubspace Sopt`. -/
theorem theorem7Min {N : ℕ}
    (B C : QSpace N →L[ℂ] QSpace N)
    (S Sopt : Finset (BitString N))
    (hB : IsMinMixerHamiltonian B S)
    (hC : IsMinPhaseSeparator C S Sopt)
    (ι : QSpace N)
    (hι : IsBottomEnergyState B S ι) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ∃ φ ∈ optimalSubspace Sopt,
        ‖quasiAdiabaticEvol (linearInterp B C) T ι - φ‖ < ε := by
  intro ε hε
  -- Step 1: Kato's theorem gives a C²-family of spectral projections P tracking the
  -- bottom eigenspace, with P(0)|ι⟩ = |ι⟩ and ran P(1) = optimalSubspace Sopt
  obtain ⟨P, hP_proj, hP_spec, hP_init, hP_final⟩ :=
    katoSpectralProjectionMin B C S Sopt hB hC ι hι
  -- Step 2: Adiabatic theorem gives ‖U_T(1)|ι⟩ - P(1)(U_T(1)|ι⟩)‖ < ε for T ≥ T₀
  obtain ⟨T₀, hT₀⟩ :=
    adiabaticTheorem (linearInterp B C) P ι hP_proj hP_spec hP_init ε hε
  -- Step 3: Package the witness φ = P(1)(U_T(1)|ι⟩)
  refine ⟨T₀, fun T hT => ?_⟩
  refine ⟨P 1 (quasiAdiabaticEvol (linearInterp B C) T ι), ?_, hT₀ T hT⟩
  -- φ ∈ optimalSubspace Sopt: P(1) is a projection, so P(1)²x = P(1)x,
  -- and hP_final characterises ran P(1) = optimalSubspace Sopt.
  apply (hP_final _).mp
  have h : (P 1 ∘L P 1) (quasiAdiabaticEvol (linearInterp B C) T ι) =
           P 1 (quasiAdiabaticEvol (linearInterp B C) T ι) := by
    rw [hP_proj 1]
  rwa [ContinuousLinearMap.comp_apply] at h
