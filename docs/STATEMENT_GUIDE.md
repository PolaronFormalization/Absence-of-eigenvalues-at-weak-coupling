# Mathematical statement and Lean correspondence

This guide records the *meaning* of the main theorem and the important boundaries of its scope. It is not an independent audit report.

## Exact contract

The declaration `Froehlich.MainStatement` in `Froehlich/TargetContract.lean` is parameterized by a family of complex-linear, possibly unbounded operators `H`. It states that there exists `gStar > 0` such that for every `g : ℝ` and `P : GW.Space`, the conditions `|g| < gStar` and `‖P‖ ≤ 1/4` imply both:

1. `realSpectrum (H g P) ∩ Set.Iio (groundEnergy (H g 0) + 1) = {groundEnergy (H g P)}`;
2. `HasEigenvector (H g P) (groundEnergy (H g P))`.

The theorem `Froehlich.main : MainStatement fiberHamiltonian` in `Froehlich/Nodes/MN03.lean` supplies the constructed physical operator family as the parameter. `GW.Space` is Euclidean `ℝ³`, and `GW.Fock.Carrier` is the bosonic Fock space.

`realSpectrum` is defined from the existence of an appropriate bounded two-sided resolvent inverse, `groundEnergy` is the infimum of this real spectrum, and `HasEigenvector` asserts the existence of a nonzero vector **in the operator domain** satisfying the eigenvalue equation. These are implemented in `Froehlich/Nodes/DF01.lean`.

## Why the fiber operator is concrete

The formal form factor is `fiberFormFactor g k = g / ‖k‖`. The uncut form factor is not square-integrable, so ordinary field-operator construction is unavailable. Instead the development defines UV-cutoff form factors and bounded cutoff interaction forms, proves their Cauchy convergence on the free-energy form space, and defines the limit `singularInteraction` (`Froehlich/Nodes/FB02A.lean`). The fiber form data (`Froehlich/Nodes/GW06.lean`) package the closed, semibounded quadratic form and construct the associated self-adjoint operator as `fiberHamiltonian` using the retained Griesemer–Wünsch functional-analytic infrastructure. The `fiberHamiltonian_domain` theorem expresses the **abstract form-identity characterization**; no Gross-transform domain formula for these momentum fibers is claimed.

## Scope and proof strategy

The momentum range includes `P=0` (the case related to Seiringer) and the coupling range includes `g=0`. The statement is the full **real spectral** exclusion below the threshold, plus existence of a ground-state eigenvector. It does **not** prove ground-state simplicity, equality of the essential-spectrum threshold, or the all-momentum corollary requiring Dahlbæk's result.

The formalization follows the broad Birman–Schwinger / Schur-complement strategy of the paper, with some rearrangements to make proof obligations manageable in Lean. These variations were suggested and implemented with assistance from ChatGPT and Codex, not in response to identified errors in the source mathematical proofs. For a longer account, see the original natural-language proof blueprint in `Froehlich-v5.tex` or `Froehlich-v5.pdf`.

## How to inspect

Run `lake env lean -j1 verification/MN03FinalInterfaces.lean` to print the main statement and axioms, and `lake env lean -j1 verification/MainDefinitionFingerprints.lean` to inspect key definitions. Source hashes are listed in `SOURCE_SHA256.txt`; the files used by the current release can be compared with that list.
