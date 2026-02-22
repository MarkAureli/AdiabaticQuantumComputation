# HANDOFF.md — AdiabaticQuantumComputation

## Project Goal

Formalize the content of [arXiv:2302.04968](https://arxiv.org/abs/2302.04968) ("Elementary Proof of QAOA
Convergence", Binkowski–Koßmann–Ziegler–Schwonnek, NJP 2024) up to and including **Theorem 7** and
its proof, then investigate and prove whether the theorem extends to minimization problems (replacing
highest energy states by ground states).

---

## Mathematical Scope

### Setting

- N-qubit Hilbert space `H := ℂ^(2^N)`
- Bit strings `Z(N) := Fin 2 ^ Fin N` (or `BitVec N`)
- Computational basis `|z⟩` identified with basis vectors
- COP: maximize `f : Z(N) → ℝ` over `S ⊆ Z(N)` (feasible set)
- Objective Hamiltonian `C := Σ_{z ∈ Z(N)} f(z) |z⟩⟨z|` (diagonal)
- Optimal solution space `Sopt := eigenspace of C|_S for its largest eigenvalue`

### Definitions to Formalize

**Definition 1 (Phase Separator Hamiltonian).**
A Hamiltonian `H ∈ L(H)` is a *phase separator* for a COP with solution space `S` and optimal space
`Sopt` iff:
1. `H` is diagonal in the computational basis.
2. The eigenspace of `H|_S` corresponding to its largest eigenvalue equals `Sopt`.

**Definition 3 (Irreducibility).**
A matrix `A ∈ Cⁿˣⁿ` is *irreducible* iff it has no proper `A`-invariant coordinate subspace of `Cⁿ`
(i.e., the only `A`-invariant coordinate subspaces are `{0}` and `Cⁿ`).

**Definition 5 (Mixer Hamiltonian).**
`B ∈ L(H)` is a *mixer* for a COP with solution space `S` iff:
1. `B(S) ⊆ S` (feasibility preservation)
2. `B|_S` is component-wise non-negative in the computational basis.
3. `B|_S` is irreducible.

### Theorems to Formalize (in order)

**Theorem 2 (Adiabatic Theorem — Teufel, without gap condition).**
Let `{H(t)}_{0≤t≤1} ⊆ L(H)` be a C²-family of self-adjoint operators. For `T > 0`, let `Ũ_T` solve
`d/ds Ũ_T(s) = -i H(s/T) Ũ_T(s)`, `Ũ_T(0) = 1`, and set `U_T(t) := Ũ_T(tT)`.
Let `P : [0,1] → L(H)` be C² with `P(t)` a projection, `H(t)P(t) = λ(t)P(t)`, and `P(t) = P(t)` for
a.e. `t`. Then:
```
lim_{T→∞} (1 - P(t)) U_T(t) P(0) = 0   uniformly in t ∈ [0,1].
```
*Note: This is imported as an axiom / sorry initially; it is the key black-box ingredient.*

**Theorem 4 (Perron–Frobenius).**
If `A ∈ Cⁿˣⁿ` is component-wise non-negative and irreducible, then `A` admits a non-degenerate
largest eigenvalue.

**Corollary 6.**
If `A ∈ Cⁿˣⁿ` is diagonal and `B ∈ Cⁿˣⁿ` is irreducible, then `A + B` is irreducible.

**Theorem 7 (Convergence of QAA).**
Consider a COP with solution space `S ⊆ H`, optimal space `Sopt ⊆ S`, and phase separator Hamiltonian
`C`. If `B ∈ L(H)` is a mixer (Def 5) and `|ι⟩ ∈ S` is a highest energy state of `B|_S`, then
```
lim_{T→∞} U_T(1)|ι⟩ ∈ Sopt,
```
where `U_T` is the quasi-adiabatic evolution w.r.t. the linear interpolation
`H(t) := (1-t)B + tC`.

### Proof Structure of Theorem 7

1. **Non-degeneracy at `t < 1`:** For `0 ≤ t₀ < 1`, apply Corollary 6 to `(1-t₀)B|_S` (irreducible)
   and `t₀C|_S` (diagonal), so `H(t₀)|_S` is non-negative + irreducible. By Perron–Frobenius,
   `λ_max(t₀)` is non-degenerate.
2. **Analytic eigenvalue curves:** `t ↦ H(t)|_S` is analytic. By Kato–Rellich, eigenvalue curves
   `{λ_m(t)}` are analytic, and spectral projections extend analytically (as C^ω) through level
   crossings (Kato [14, Thm 6.1]).
3. **Tracking `λ_max`:** Non-degeneracy for `t ∈ [0,1)` implies the top eigenvalue curve `λ₁ ≡ λ_max`
   on `[0,1]` by continuity. The associated spectral projection `P₁` is C² on `[0,1]`.
4. **Apply Adiabatic Theorem:** Since `|ι⟩` is in `ran(P₁(0))` (highest energy state of `B|_S`),
   Theorem 2 gives `lim_{T→∞} U_T(1)|ι⟩ ∈ ran(P₁(1)) = Sopt`.

---

## Central Research Question

> **Can Theorem 7 be extended to minimization?**
> That is: if `|ι⟩` is a *lowest* energy state of `B|_S` and `C` encodes a *minimization* problem
> (so `Sopt` = eigenspace of `C|_S` for its *smallest* eigenvalue), does
> `lim_{T→∞} U_T(1)|ι⟩ ∈ Sopt` still hold?

**The obstruction:** The Perron–Frobenius theorem guarantees non-degeneracy of the *largest*
eigenvalue of non-negative irreducible matrices. The same does not hold for the smallest eigenvalue
in general — P-F says nothing about it.

**The fix (expected approach):** Note that if `B|_S` is non-negative irreducible and `C|_S` is diagonal,
then `-B|_S` has all non-positive off-diagonal entries ("Metzler / Z-matrix" structure). The key is
whether `H(t)|_S = (1-t)B|_S + tC|_S` (now with C encoding minimization, so perhaps negating f) can
be reformulated so that P-F still applies. One route: replace `B` by `-B` and `C` by `-C` (pass to the
negated problem), but then component-wise non-negativity of `B|_S` becomes non-positivity of `-B|_S`,
which breaks P-F. A second route: impose the additional condition that `-C|_S` has non-negative
diagonal, so that `(1-t)B|_S - tC|_S` is non-negative and irreducible for `t < 1`.

The goal is to **prove** a precise minimization analogue of Theorem 7 in Lean.

---

## Implementation Plan

### Phase 1 — Foundations
- [ ] Define `BitString N`, computational basis, `H_N := EuclideanSpace ℂ (Fin (2^N))`
- [ ] Define diagonal Hamiltonians and matrix representation
- [ ] Define irreducibility for matrices over `ℂ` (or `ℝ`-matrices)
- [ ] State and sorry Perron–Frobenius (Theorem 4)
- [ ] Prove Corollary 6

### Phase 2 — QAA Definitions
- [ ] Define `PhaseSeparator` (Def 1)
- [ ] Define `MixerHamiltonian` (Def 5)
- [ ] Define linear interpolation `H_lin(B,C)(t)`
- [ ] Define quasi-adiabatic evolution `U_T` (as an axiom/sorry for now)

### Phase 3 — Theorem 7
- [ ] State and sorry Adiabatic Theorem (Theorem 2)
- [ ] State and sorry analytic perturbation theory lemma (Kato [14, Thm 6.1])
- [ ] Prove Theorem 7 modulo sorryed lemmas

### Phase 4 — Minimization Extension
- [ ] Identify precise conditions under which the minimization analogue holds
- [ ] Adapt the proof: find the right P-F-like lemma for lowest eigenvalue
- [ ] Prove the minimization version of Theorem 7

---

## Key Dependencies / Mathlib Candidates

- `Matrix.IsIrreducible` — check if exists in Mathlib
- `Perron–Frobenius` — check Mathlib (may need to sorry)
- `ContinuousLinearMap`, `EuclideanSpace ℂ` — for Hilbert space setup
- `SchrodingerEquation` / `MeasureTheory.ODE` — for time evolution
- Analytic perturbation theory — likely sorry or cited as axiom

---

## Session Log

### 2026-02-22 — Initial setup

- Scaffolded Lean 4 project with Mathlib dependency
- Initialized beads issue tracker
- Created HANDOFF.md with full mathematical scope from arXiv:2302.04968
- Identified central research question (maximization → minimization)

### 2026-02-22 — Phase 1 start: Hilbert space foundations

Completed `AdiabaticQuantumComputation-2ww` (Define BitString, computational basis, N-qubit Hilbert space).

**What was done:**
- `BitString N := Fin (2^N)` — indexes the 2^N computational basis states.
- `QSpace N := EuclideanSpace ℂ (BitString N)` — the N-qubit Hilbert space.
- `ket z := EuclideanSpace.single z 1` — the computational basis vector `|z⟩`.
- `orthonormal_ket` — proved via `EuclideanSpace.orthonormal_single` (one-liner).
- `ket_norm`, `ket_inner` — proved as direct corollaries.
- Key lesson: the inner product notation `⟪·, ·⟫_ℂ` is not parsed by Lean in theorem statements
  without an explicit `open` or import; use `inner ℂ` directly.

**Now unblocked:**
- `AdiabaticQuantumComputation-vm1`: Define diagonal Hamiltonians and matrix representation
- `AdiabaticQuantumComputation-aa9`: Define irreducibility for matrices (Def 3)

**Next steps:** ~~Work both `vm1` and `aa9` in parallel~~ — completed in next session.

### 2026-02-22 — Phase 1 cont: diagonal Hamiltonians and irreducibility

Completed `AdiabaticQuantumComputation-vm1` and `AdiabaticQuantumComputation-aa9` in parallel.

**vm1 — DiagonalHamiltonian.lean:**
- `diagonalOp f` — `QSpace N →L[ℂ] QSpace N` via `EuclideanSpace.equiv` + pointwise scaling.
- `diagonalOp_apply` — pointwise: `(diagonalOp f v) z = f(z) * v(z)`.
- `diagonalOp_ket` — basis action: `diagonalOp f (ket z) = f(z) • ket z`.
- `objectiveHamiltonian f` — real-eigenvalue version: `diagonalOp (fun z => (f z : ℂ))`.
- `IsDiagonal` predicate and instances for `diagonalOp`, `objectiveHamiltonian`.
- Key proof pattern: `ext i; simp [diagonalOp_apply, EuclideanSpace.single_apply]; split_ifs`.

**aa9 — Irreducibility.lean:**
- `IsCoordIrreducible A` — paper's Def 3: for every proper nonempty `S`, ∃ i ∉ S, j ∈ S with A i j ≠ 0.
- `Matrix.IsIrreducible.isCoordIrreducible` — Mathlib's P-F irreducibility implies ours (sorry).
- Mathlib's `Matrix.IsIrreducible` (from `Mathlib.LinearAlgebra.Matrix.Irreducible.Defs`)
  bundles non-negativity + strong connectivity; already exists and is imported.

**Infrastructure fix:** Added `/opt/homebrew/bin` to PATH in `.mcp.json` so `lean_local_search` works.

**Now unblocked (5 issues):**
- `AdiabaticQuantumComputation-497`: Define linear interpolation H_lin(B,C)(t)
- `AdiabaticQuantumComputation-75m`: Define PhaseSeparator Hamiltonian (Def 1)
- `AdiabaticQuantumComputation-jjr`: Define MixerHamiltonian (Def 5)
- `AdiabaticQuantumComputation-qmx`: State Perron-Frobenius theorem (Thm 4, sorry)
- `AdiabaticQuantumComputation-xch`: Prove Corollary 6: diagonal + irreducible → irreducible

**Next priority:** `xch` (Corollary 6) and `qmx` (P-F sorry) can proceed now. `75m` and `jjr`
(Phase 2 definitions) are also unblocked.

### 2026-02-22 — Phase 1 cont: Corollary 6

Completed `AdiabaticQuantumComputation-xch`.

**What was done:**
- Added `import Mathlib.LinearAlgebra.Matrix.IsDiag` to `Irreducibility.lean`.
- Proved `isCoordIrreducible_add_of_isDiag_left`: if `A.IsDiag` and `B` is
  `IsCoordIrreducible`, then `A + B` is `IsCoordIrreducible`.
- Proof: for any proper nonempty S, B-irreducibility gives `i ∉ S`, `j ∈ S`, `B i j ≠ 0`;
  then `i ≠ j` (membership), so `A i j = 0` by `hA hij`, hence `(A+B) i j = B i j ≠ 0`.
- Key lemma: `Matrix.IsDiag` = `Pairwise (fun i j => A i j = 0)`, so `hA hij : A i j = 0`.

**Remaining open (4 issues):**
- `qmx`: State P-F theorem as sorry
- `75m`: Define PhaseSeparator Hamiltonian (Def 1)
- `jjr`: Define MixerHamiltonian (Def 5)
- `497`: Define linear interpolation H_lin(B,C)(t)
