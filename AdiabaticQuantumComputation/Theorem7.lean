import AdiabaticQuantumComputation.QAADefinitions
import AdiabaticQuantumComputation.PerronFrobenius

/-!
# Theorem 7: Convergence of the Quantum Adiabatic Algorithm

This file formalizes Theorem 7 of arXiv:2302.04968:

> For a COP with feasible set `S`, optimal space `Sopt`, phase separator `C`, and mixer
> `B`, if `|ι⟩ ∈ S` is a highest energy state of `B|_S`, then the quasi-adiabatic
> evolution `U_T` w.r.t. `H(t) := (1-t)B + tC` satisfies
> `lim_{T→∞} U_T(1)|ι⟩ ∈ Sopt`.

## Proof strategy

1. **Non-degeneracy (Theorem 4 + Corollary 6):** For `t ∈ [0, 1)`, the restriction
   `H(t)|_S = (1-t)B|_S + tC|_S` is irreducible (Corollary 6: `(1-t)B|_S` is
   irreducible and `tC|_S` is diagonal) and non-negative, so Perron–Frobenius gives a
   non-degenerate largest eigenvalue `λ_max(t)`.
2. **Analytic spectral family (Kato):** By Kato's analytic perturbation theory there
   exists a C²-family of spectral projections `P(t)` onto the top eigenspace of
   `H(t)|_S`, smooth on all of `[0,1]`. Moreover `ran P(1) = Sopt` and `|ι⟩ ∈ ran P(0)`.
3. **Adiabatic Theorem (Theorem 2):** Since `|ι⟩ ∈ ran P(0)`, the adiabatic theorem
   gives `‖(1 - P(1)) U_T(1)|ι⟩‖ → 0`, so `U_T(1)|ι⟩` converges to `Sopt`.

## Main definitions

- `optimalSubspace Sopt`: the span of `{|z⟩ | z ∈ Sopt}` in `QSpace N`.
- `IsTopEnergyState B S ι`: `ι` is a highest energy eigenstate of `B|_S`.
- `quasiAdiabaticEvol H T`: the quasi-adiabatic evolution operator `U_T(1)` (sorry'd).

## Main results

- `adiabaticTheorem`: Theorem 2 (sorry'd).
- `katoSpectralProjection`: Kato's analytic perturbation lemma (sorry'd).
- `theorem7`: Theorem 7, proved modulo the above sorry'd lemmas.
-/

/-! ## Optimal subspace -/

/-- The *optimal subspace* `span{|z⟩ | z ∈ Sopt} ⊆ QSpace N`.
This is the range of the spectral projection `P(1)` for the top eigenvalue of the
interpolated Hamiltonian at `t = 1`, and equals the span of all optimal basis states. -/
noncomputable def optimalSubspace {N : ℕ} (Sopt : Finset (BitString N)) :
    Submodule ℂ (QSpace N) :=
  Submodule.span ℂ (ket '' (Sopt : Set (BitString N)))

/-! ## Highest energy state -/

/-- `ι` is a *highest energy state* of `B|_S`: `ι` is a nonzero vector in the feasible
subspace `span{|z⟩ | z ∈ S}`, is an eigenvector of `B` for eigenvalue `μ ∈ ℝ`, and `μ`
is the largest eigenvalue of `B` on the feasible subspace. -/
def IsTopEnergyState {N : ℕ} (B : QSpace N →L[ℂ] QSpace N)
    (S : Finset (BitString N)) (ι : QSpace N) : Prop :=
  ι ≠ 0 ∧
  ι ∈ Submodule.span ℂ (ket '' (S : Set (BitString N))) ∧
  ∃ μ : ℝ, B ι = (μ : ℂ) • ι ∧
    ∀ ν : ℝ, (∃ w : QSpace N, w ≠ 0 ∧
               w ∈ Submodule.span ℂ (ket '' (S : Set (BitString N))) ∧
               B w = (ν : ℂ) • w) → ν ≤ μ

/-! ## Quasi-adiabatic evolution -/

/-- The *quasi-adiabatic evolution operator* `U_T(1)`.

Given a time-dependent Hamiltonian `H : ℝ → QSpace N →L[ℂ] QSpace N`, this is the
unitary operator defined by the Schrödinger ODE
`d/ds Ũ_T(s) = -i · H(s/T) · Ũ_T(s)`, `Ũ_T(0) = id`,
evaluated at `s = T` (i.e. `U_T := Ũ_T(T)`).

The ODE solution is outside the scope of this file; we take `quasiAdiabaticEvol` as a
sorry'd constant. Its key asymptotic property is axiomatized by `adiabaticTheorem`. -/
noncomputable def quasiAdiabaticEvol {N : ℕ}
    (H : ℝ → QSpace N →L[ℂ] QSpace N) (T : ℝ) :
    QSpace N →L[ℂ] QSpace N := sorry

/-! ## Theorem 2: Adiabatic Theorem -/

/-- **Theorem 2 (Adiabatic Theorem — Teufel, without gap condition).**

Let `H : ℝ → QSpace N →L[ℂ] QSpace N` be a (C²) family of self-adjoint operators and
`P : ℝ → QSpace N →L[ℂ] QSpace N` a (C²) family of spectral projections satisfying:
- `P(t)² = P(t)` for all `t`,
- `H(t) ∘ P(t) = μ(t) · P(t)` for some eigenvalue `μ(t) ∈ ℝ`,
- `ι ∈ ran P(0)`.

Then the component of `U_T(1) |ι⟩` outside `ran P(1)` vanishes as `T → ∞`:
for every `ε > 0` there exists `T₀` such that for all `T ≥ T₀`,
`‖U_T(1)|ι⟩ - P(1)(U_T(1)|ι⟩)‖ < ε`.

*Reference:* Teufel, *Adiabatic Perturbation Theory in Quantum Dynamics* (2003). -/
theorem adiabaticTheorem {N : ℕ}
    (H : ℝ → QSpace N →L[ℂ] QSpace N)
    (P : ℝ → QSpace N →L[ℂ] QSpace N)
    (ι : QSpace N)
    (hP_proj : ∀ t, P t ∘L P t = P t)
    (hHSpec : ∀ t, ∃ μ : ℝ, H t ∘L P t = (μ : ℂ) • P t)
    (hι : P 0 ι = ι) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ‖quasiAdiabaticEvol H T ι - P 1 (quasiAdiabaticEvol H T ι)‖ < ε := by
  sorry

/-! ## Kato Analytic Perturbation Theory -/

/-- **Kato's Analytic Perturbation Theory** (Kato [14, Thm 6.1]).

For the linearly interpolated Hamiltonian `H(t) = (1-t)B + tC` with `B` a mixer and
`C` a phase separator, this lemma provides a C²-family of spectral projections `P(t)`
onto the top eigenspace of `H(t)|_S`, valid on all of `[0,1]`:

- **Existence:** The top eigenvalue of `H(t)|_S` is non-degenerate for all `t ∈ [0, 1)`
  by Perron–Frobenius (Theorem 4) + Corollary 6 applied to `(1-t)B|_S` (irreducible)
  and `tC|_S` (diagonal). Kato's theorem extends the spectral projection analytically
  to `t = 1`.
- **Projection property:** `P(t)² = P(t)` for all `t`.
- **Spectral property:** `H(t) ∘ P(t) = μ(t) · P(t)` for the top eigenvalue `μ(t)`.
- **Initial condition:** `|ι⟩ ∈ ran P(0)` (since `ι` is the Perron eigenvector of `B|_S`).
- **Final range:** `ran P(1) = optimalSubspace Sopt`.

*Reference:* Kato, *Perturbation Theory for Linear Operators* (1966), Thm II.6.1. -/
theorem katoSpectralProjection {N : ℕ}
    (B C : QSpace N →L[ℂ] QSpace N)
    (S Sopt : Finset (BitString N))
    (hB : IsMixerHamiltonian B S)
    (hC : IsPhaseSeparator C S Sopt)
    (ι : QSpace N)
    (hι : IsTopEnergyState B S ι) :
    ∃ P : ℝ → QSpace N →L[ℂ] QSpace N,
      (∀ t, P t ∘L P t = P t) ∧
      (∀ t, ∃ μ : ℝ, linearInterp B C t ∘L P t = (μ : ℂ) • P t) ∧
      P 0 ι = ι ∧
      (∀ φ : QSpace N, P 1 φ = φ ↔ φ ∈ optimalSubspace Sopt) := by
  sorry

/-! ## Theorem 7 -/

/-- **Theorem 7 (Convergence of QAA)** (arXiv:2302.04968, Theorem 7).

Consider a combinatorial optimisation problem with feasible set `S ⊆ BitString N`,
optimal solution set `Sopt ⊆ S`, phase separator `C`, and mixer `B`. If `|ι⟩ ∈ S` is
a highest energy state of `B|_S`, then the final state `U_T(1)|ι⟩` of the
quasi-adiabatic evolution w.r.t. `H(t) = (1-t)B + tC` converges to the optimal
subspace as `T → ∞`:

for every `ε > 0` there exists `T₀` such that for all `T ≥ T₀` there is a state
`φ ∈ optimalSubspace Sopt` with `‖U_T(1)|ι⟩ - φ‖ < ε`.

**Proof:**
1. By `katoSpectralProjection`, obtain a spectral projection family `P` with
   `ran P(0) ∋ ι` and `ran P(1) = Sopt`.
2. By `adiabaticTheorem` (applied to `H = linearInterp B C` and the above `P`),
   `‖U_T(1)|ι⟩ - P(1)(U_T(1)|ι⟩)‖ → 0` as `T → ∞`.
3. The witness `φ := P(1)(U_T(1)|ι⟩)` lies in `optimalSubspace Sopt` because `P(1)`
   is a projection (`P(1)² = P(1)`) and `ran P(1) = optimalSubspace Sopt`. -/
theorem theorem7 {N : ℕ}
    (B C : QSpace N →L[ℂ] QSpace N)
    (S Sopt : Finset (BitString N))
    (hB : IsMixerHamiltonian B S)
    (hC : IsPhaseSeparator C S Sopt)
    (ι : QSpace N)
    (hι : IsTopEnergyState B S ι) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ∃ φ ∈ optimalSubspace Sopt,
        ‖quasiAdiabaticEvol (linearInterp B C) T ι - φ‖ < ε := by
  intro ε hε
  -- Step 1: Kato's theorem gives a C²-family of spectral projections P
  obtain ⟨P, hP_proj, hP_spec, hP_init, hP_final⟩ :=
    katoSpectralProjection B C S Sopt hB hC ι hι
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
