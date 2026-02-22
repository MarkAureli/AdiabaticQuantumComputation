# AdiabaticQuantumComputation

A Lean 4 / Mathlib formalization of results in adiabatic quantum computation, based on:

> **Elementary Proof of QAOA Convergence**
> Lennart Binkowski, Gereon Koßmann, Timo Ziegler, René Schwonnek
> *New Journal of Physics* 26 (2024) 073001 — [arXiv:2302.04968](https://arxiv.org/abs/2302.04968)

## Scope

The formalization covers the content of the paper up to and including **Theorem 7** (Convergence of the
Quantum Adiabatic Algorithm) and its proof. The central research question is whether the theorem
extends to minimization problems — i.e., whether highest energy states can be replaced by ground
states.

Key results:

- Perron–Frobenius theorem for non-negative irreducible matrices (Theorem 4)
- Convergence of the QAA via Teufel's adiabatic theorem without gap condition (Theorem 7)
- Minimization analogue of Theorem 7 (research contribution)

## Building

```bash
lake build AdiabaticQuantumComputation 2>&1 | tail -40
```

**Do not run bare `lake build`** — it rebuilds all of Mathlib (~2 hours).

## Structure

- `AdiabaticQuantumComputation/Basic.lean` — main source
- `HANDOFF.md` — mathematical scope, implementation plan, and session log
