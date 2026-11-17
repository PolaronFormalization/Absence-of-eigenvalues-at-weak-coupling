# Lean formalization of the absence of excited eigenvalues for the Fröhlich polaron at weak coupling

A Lean 4 formalization of a spectral result for the three-dimensional Fröhlich fiber Hamiltonian, based on the works

>D. Mitrouskas, Absence of Excited Bound States for All Fibers of the Fröhlich Polaron at Weak Coupling, arXiv:2611.09586.

and

>R. Seiringer, Absence of excited eigenvalues for Fröhlich type polaron models at weak coupling, arXiv:2210.17123, J. Spectr. Theory 13 (2023), 1045–1055.

The formalization establishes the absence of excited eigenvalues of the Fröhlich fiber Hamiltonian for weak-coupling and all momenta (|P|\leq 1/4). It was obtained with assistance from ChatGPT and Codex (OpenAI). The proofs do not follow the original arguments line by line, but include modifications made to facilitate formal verification. The expanded and modified natural-language proof blueprint (obtained by ChatGPT) is included in [`docs/Froehlich-v5.pdf`](docs/Froehlich-v5.pdf) and [LaTeX source](docs/Froehlich-v5.tex).

## Main result

The designated theorem is [`Froehlich.main`](Froehlich/Nodes/MN03.lean), of type `MainStatement fiberHamiltonian`. Here \(H_g(P)\) denotes the self-adjoint Fröhlich fiber Hamiltonian, constructed within the formalization, and \(E_g(P)=\inf\sigma(H_g(P))\) its ground-state energy.

The theorem establishes the existence of a constant \(g_*>0\) such that, for every real coupling \(g\) with \(|g|<g_*\) and every momentum \(P\in\mathbb R^3\) with \(|P|\leq 1/4\), the following hold:

1. **Spectral equality:**
   \[
   \sigma(H_g(P))\cap(-\infty,E_g(0)+1)
   =\{E_g(P)\}.
   \]

2. **Ground-state existence:** There exists a nonzero \(\psi\in D(H_g(P))\) satisfying
   \[
   H_g(P)\psi=E_g(P)\psi.
   \]

Here \(H_g(P)\) denotes the self-adjoint Fröhlich fiber Hamiltonian, whose construction is also part of the Lean formalization. The formalization does not yet include the identification of \(E_g(0)+1\) as the bottom of the essential spectrum, the simplicity of the ground-state eigenvalue, or the extension of the absence of excited eigenvalues to arbitrary momenta using Dahlbæk's results. We expect to address these remaining results in future formalization projects.

| Mathematical object or claim | Lean declaration | Source file |
| --- | --- | --- |
| Exact theorem contract | `Froehlich.MainStatement` | [`Froehlich/TargetContract.lean`](Froehlich/TargetContract.lean) |
| Main formal theorem | `Froehlich.main` | [`Froehlich/Nodes/MN03.lean`](Froehlich/Nodes/MN03.lean) |
| Fröhlich form factor and UV cutoff | `fiberFormFactor`, `cutoffFormFactor` | [`Froehlich/Nodes/GW05.lean`](Froehlich/Nodes/GW05.lean) |
| Limiting singular interaction form | `singularInteraction` | [`Froehlich/Nodes/FB02A.lean`](Froehlich/Nodes/FB02A.lean) |
| Fiber form data and operator | `fiberFormData`, `fiberHamiltonian` | [`Froehlich/Nodes/GW06.lean`](Froehlich/Nodes/GW06.lean) |
| Self-adjointness and abstract domain identity | `fiberHamiltonian_selfadjoint`, `fiberHamiltonian_domain` | [`Froehlich/Nodes/GW06.lean`](Froehlich/Nodes/GW06.lean) |
| Spectrum and ground energy | `realSpectrum`, `groundEnergy`, `HasEigenvector` | [`Froehlich/Nodes/DF01.lean`](Froehlich/Nodes/DF01.lean) |

For mathematical interpretation and scope, see [`docs/STATEMENT_GUIDE.md`](docs/STATEMENT_GUIDE.md).

## Verify

**Requirements:** Lean installed via [elan](https://lean-lang.org/install/), Git, and a working network connection for initial dependencies. The project pins Lean `leanprover/lean4:v4.36.0-rc2` in `lean-toolchain` and Mathlib at commit `9bac2d0692944a775113f7c130fd5e5b4608a854` in the unchanged Lake files.

From the repository root:

```sh
lake exe cache get
bash scripts/check.sh
```

The script builds the `GW` and `Froehlich` elaboration targets, then asks Lean to print the main theorem, its transitive axioms, and fingerprints of the key definitions. To run the individual checks:

```sh
lake build GW:elabArts Froehlich:elabArts
lake env lean -j1 verification/MN03FinalInterfaces.lean
lake env lean -j1 verification/MainDefinitionFingerprints.lean
```

The source project's recorded axiom inspection reports only Lean's standard foundational axioms `propext`, `Classical.choice`, and `Quot.sound` for `Froehlich.main`. A text scan of the retained production Lean files in this release found no `sorry`, `admit`, custom `axiom`, `unsafe`, `opaque`, or `native_decide`. Please rerun the commands above to inspect the theorem in your environment.

**Verification status:** The author reported a successful local build of the original project (9,202 jobs), followed by a direct successful Lean check of the main theorem file. This trimmed release preserves the Lean source files and locked dependencies byte-for-byte, but has *not* been freshly compiled in the environment used to package it. The included GitHub Actions workflow is a proposed reproducibility check; its first run should be inspected after publication. No external independent review is claimed.

## Mathematical and software structure

- [`Froehlich/`](Froehlich/) and [`Froehlich.lean`](Froehlich.lean): fiber Hamiltonians, estimates, spectral reduction, and final theorem.
- [`GW/`](GW/) and [`GW.lean`](GW.lean): retained Lean development based on Griesemer–Wünsch, *Self-Adjointness and Domain of the Fröhlich Hamiltonian*, [arXiv:1508.02533](https://arxiv.org/abs/1508.02533).
- [`docs/`](docs/): mathematical proof blueprint and explanation of the paper-to-Lean correspondence.
- [`verification/`](verification/) and [`scripts/`](scripts/): Lean statement/axiom inspection and reproducibility scripts.
- [`.github/workflows/lean.yml`](.github/workflows/lean.yml): automatic build and axiom-report job for GitHub Actions.

The Griesemer–Wünsch paper concerns the **full Hamiltonian**. Its form-operator framework is reused in the *separate construction of fiber Hamiltonians* in this project; the paper does not itself supply the fiber construction. The domain theorem here is an abstract quadratic-form representation identity, **not** an explicit Gross-transform description of the domain of a fiber Hamiltonian.

The detailed blueprint `docs/Froehlich-v5.tex` was prepared as a natural-language mathematical guide for the formalization; it is not itself a kernel-checked certificate. Its references to internal preparation bundles reflect the archived development process. These historical bundles and logs were deliberately omitted from the public source release.

## Source provenance and limits

`docs/SOURCE_SHA256.txt` records the SHA-256 hashes of all retained Lean, configuration, verification, and blueprint files. They are unchanged from the supplied pre-release archive. This repository does not include build caches (`.lake`), duplicate GW input bundles, machine-specific compilation wrappers, internal planning logs, or Codex session files. The root import `Froehlich.lean` retains one historical comment about MN03 not yet being implemented; the comment is outdated, but the file is kept byte-identical to the locally checked snapshot. The final theorem is present in `Froehlich/Nodes/MN03.lean`.

## License and attribution

The repository is prepared for release under the **Apache License, Version 2.0** (`Apache-2.0`); see [`LICENSE`](LICENSE). This license covers contributions whose copyright holders have authorized release under these terms. The original research papers cited above are referenced, not relicensed here.

The retained `GW/` development originated in a **separate Lean formalization** based on Griesemer–Wünsch. Its original release archive did not specify an open-source license. **Before publishing this repository**, the responsible copyright holder(s) must confirm that the retained `GW` source may be distributed under Apache-2.0 (or provide its existing license and attribution terms). Adding a repository-level license does not itself grant rights over someone else's code. Please cite the mathematical papers when using their results.
