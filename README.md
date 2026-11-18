# Absence of excited eigenvalues for the Fröhlich polaron at weak coupling — Lean 4 formalization

[![Lean verification](https://github.com/PolaronFormalization/Absence-of-eigenvalues-at-weak-coupling/actions/workflows/lean.yml/badge.svg)](https://github.com/PolaronFormalization/Absence-of-eigenvalues-at-weak-coupling/actions/workflows/lean.yml)

A Lean 4 / Mathlib formalization of the main results from

> D. Mitrouskas, *Absence of Excited Bound States for All Fibers of the Fröhlich Polaron at Weak Coupling*, [arXiv:2611.09586](https://arxiv.org/abs/2611.09586).

> R. Seiringer, *Absence of excited eigenvalues for Fröhlich type polaron models at weak coupling*, [arXiv:2210.17123](https://arxiv.org/abs/2210.17123), J. Spectr. Theory **13** (2023), 1045–1055.

This formalization project proves the absence of excited eigenvalues of the Fröhlich fiber Hamiltonian for weak coupling and all momenta `|P| ≤ 1/4`. The code was obtained with assistance from ChatGPT and Codex. The proofs do not follow the original arguments line by line, but include modifications made to facilitate the formal verification. An expanded and modified natural-language proof blueprint is included in [`docs/Froehlich-v5.pdf`](docs/Froehlich-v5.pdf).

## Scope of the formalization

The designated theorem is [`Froehlich.main`](Froehlich/Nodes/MN03.lean). Here `H_g(P)` denotes the self-adjoint Fröhlich fiber Hamiltonian, constructed within the formalization, and `E_g(P) = inf σ(H_g(P))` its ground-state energy.

The theorem establishes the existence of a constant `g_* > 0` such that, for every real coupling `g` with `|g| < g_*` and every momentum `P ∈ ℝ³` with `|P| ≤ 1/4`, the following hold:

1. **Absence of excited eigenvalues:**

   `σ(H_g(P)) ∩ (-∞, E_g(0) + 1) = {E_g(P)}`.

2. **Existence of a ground-state:** There exists a nonzero `ψ ∈ D(H_g(P))` satisfying

   `H_g(P)ψ = E_g(P)ψ`.



We note that the formalization does **not** establish:

   - Simplicity of the ground-state eigenvalue
   - Identification of the essential spectrum with `[E_g(0)+1,\infty))`
   - The all-momentum statement of Corollary 1.2
   - The general class of Fröhlich-type models covered by Seiringer's paper

## Results

The main theorem is proved in Lean 4 using Mathlib. Its proof uses only Lean's standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`). The project contains no `sorry` or custom mathematical axioms.

The following table lists the main definitions and proved results underlying the construction of the Fröhlich fiber Hamiltonian and the proof of the main theorem, together with their corresponding Lean declarations and source files.

| Mathematical object or result | Type | Lean declaration | Source file |
| --- | --- | --- | --- |
| Main theorem | Theorem | `Froehlich.main` | [`TargetContract.lean`](Froehlich/TargetContract.lean) (statement), [`MN03.lean`](Froehlich/Nodes/MN03.lean) (proof) |
| Fröhlich form factor and UV cutoff | Definitions | `fiberFormFactor`, `cutoffFormFactor` | [`GW05.lean`](Froehlich/Nodes/GW05.lean) |
| Singular interaction and cutoff convergence | Definition + Theorem | `singularInteraction`, `cutoffInteraction_tendsto` | [`FB02A.lean`](Froehlich/Nodes/FB02A.lean) |
| Fiber Hamiltonian, self-adjointness and domain | Definitions + Theorems | `fiberFormData`, `fiberHamiltonian`, `fiberHamiltonian_selfadjoint`, `fiberHamiltonian_domain` | [`GW06.lean`](Froehlich/Nodes/GW06.lean) |
| Spectrum, ground-state energy and eigenvectors | Definitions | `realSpectrum`, `groundEnergy`, `HasEigenvector` | [`DF01.lean`](Froehlich/Nodes/DF01.lean) |


## How to read the formalization

The precise statement of the main theorem is defined in [`TargetContract.lean`](Froehlich/TargetContract.lean) as `Froehlich.MainStatement`, parameterized by a family of operators `H`. The theorem [`Froehlich.main`](Froehlich/Nodes/MN03.lean) proves `MainStatement fiberHamiltonian`, where `fiberHamiltonian` is the constructed Fröhlich fiber Hamiltonian. Here `GW.Space` denotes Euclidean `ℝ³`, and `GW.Fock.Carrier` the bosonic Fock space.

The definitions `realSpectrum`, `groundEnergy`, and `HasEigenvector` are implemented in [`DF01.lean`](Froehlich/Nodes/DF01.lean). The spectrum is defined through the resolvent set, the ground-state energy as the infimum of the spectrum, and the eigenvector predicate requires a nonzero vector in the operator domain satisfying the eigenvalue equation.

### Construction of the fiber Hamiltonian

The construction of the fiber Hamiltonian is part of the formalization. The Fröhlich form factor `fiberFormFactor g k = g / ‖k‖` is not square-integrable, so the interaction cannot be defined directly as an ordinary field operator.

Instead, the formalized proof introduces ultraviolet-cutoff form factors and the corresponding interaction forms, proves their convergence on the free-energy form space, and defines the limiting singular interaction `singularInteraction` in [`FB02A.lean`](Froehlich/Nodes/FB02A.lean).

The resulting closed, semibounded quadratic form determines the self-adjoint operator `fiberHamiltonian`, constructed in [`GW06.lean`](Froehlich/Nodes/GW06.lean). This construction follows the quadratic-form approach of [Griesemer and Wünsch](https://arxiv.org/abs/1508.02533) for the full Fröhlich Hamiltonian. The functional-analytic framework from our separate [Lean formalization of their results](https://github.com/PolaronFormalization/GW-Froehlich-formalization) is incorporated into the present repository under [`GW/`](GW/). The fiber Hamiltonians are then constructed and their self-adjointness established in [`GW06.lean`](Froehlich/Nodes/GW06.lean).

## Build and check

Install Lean with [elan](https://github.com/leanprover/elan). The project uses Lean `v4.36.0-rc2` (`lean-toolchain`), and the exact dependency revisions are pinned in `lake-manifest.json`.

Clone the repository and enter its directory:

```bash
git clone https://github.com/PolaronFormalization/Absence-of-eigenvalues-at-weak-coupling.git
cd Absence-of-eigenvalues-at-weak-coupling
```

Then prepare the dependencies and build the formalization:

```bash
lake exe cache get   # Download precompiled Mathlib files
lake build GW:elabArts Froehlich:elabArts   # Build the formalization
```

To inspect the main theorem, its axioms, and the relevant definitions, run:

```bash
lake env lean -j1 verification/MN03FinalInterfaces.lean
lake env lean -j1 verification/MainDefinitionFingerprints.lean
```

The first command prints the main theorem `Froehlich.main` and its foundational axioms (`propext`, `Classical.choice`, `Quot.sound`). The second checks the definitions underlying the formalized statement.

The complete project has also been successfully verified on [GitHub Actions](https://github.com/PolaronFormalization/Absence-of-eigenvalues-at-weak-coupling/actions).


## License

The Lean code is released under the Apache License 2.0 license (see [`LICENSE`](LICENSE)). The mathematical results are described in the papers cited above. If you use this formalization, please cite the corresponding papers and reference this repository.
