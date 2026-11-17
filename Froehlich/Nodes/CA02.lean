import Froehlich.Nodes.CA02OperatorMultiIndex

set_option autoImplicit false

/-!
CA02 / lem:weightderivatives, source1487–1514.
* exists_scalarWeightMultiIndexExpansion: actual scalar formula, finite
  coefficients independent b,x, exact |beta|+r=2j and j≤r, source Cr recurrence.
* scalarWeightMultiIndex_relative_bound: literal relative scalar bound.
* auxiliaryPhysicalFreeInverse_contDiff and multiPartial_norm_le: native
  physical source G is norm C3 with the canonical Cr derivative bounds.
* auxiliaryFixedEnergyWeightJet_zero_contDiff, zero_multiPartial_norm_le,
  and zero_physical: the SAME G in the fixed actual weighted energy target,
  norm C3 with exact local2Cr bounds. All constants precede e,g,p.
-/
noncomputable section
namespace Froehlich
open scoped BoundedEndReal
local instance ca02HighNormedGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n) :=
  Submodule.normedAddCommGroup (HighSectorSpace n)
local instance ca02EndNormedGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance ca02EndRealNormedSpace (n : ℕ) : NormedSpace ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  (BoundedEndReal.realNormedAlgebra (E := HighSectorSpace n)).toNormedSpace
local instance ca02EndRealBoundedSMul (n : ℕ) : IsBoundedSMul ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  NormedSpace.toIsBoundedSMul
local instance ca02EndRealContinuousSMul (n : ℕ) : ContinuousSMul ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  IsBoundedSMul.continuousSMul

local instance ca02EnergyNormedGroup (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) :
    NormedAddCommGroup (AuxiliaryEnergySpace n e p0 he) :=
  Submodule.normedAddCommGroup (AuxiliaryEnergySpace n e p0 he)
local instance ca02EnergyMapNormedGroup (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) :
    NormedAddCommGroup (HighSectorSpace n →L[ℂ] AuxiliaryEnergySpace n e p0 he) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance ca02EnergyMapRealNormedSpace (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) :
    NormedSpace ℝ (HighSectorSpace n →L[ℂ] AuxiliaryEnergySpace n e p0 he) :=
  NormedSpace.restrictScalars ℝ ℂ _
local instance ca02EnergyMapRealBoundedSMul (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) :
    IsBoundedSMul ℝ (HighSectorSpace n →L[ℂ] AuxiliaryEnergySpace n e p0 he) :=
  NormedSpace.toIsBoundedSMul
local instance ca02EnergyMapRealContinuousSMul (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) :
    ContinuousSMul ℝ (HighSectorSpace n →L[ℂ] AuxiliaryEnergySpace n e p0 he) :=
  IsBoundedSMul.continuousSMul

theorem finalCA02 (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (n : ℕ) (_hn : n ≤ 2) :
    ContDiff ℝ 3 (fun p : GW.Space => auxiliaryPhysicalFreeInverse n e p he.2) ∧
    (∀ alpha : Fin 3 → ℕ, (∑ i, alpha i) ≤ 3 → ∀ p : Fin 3 → ℝ,
      ‖coordinateMultiPartial alpha
        (fun q => auxiliaryPhysicalFreeInverse n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm q) he.2) p‖ ≤
        scalarDerivativeCoefficientBound (∑ i, alpha i)) ∧
    (∀ p0 : GW.Space,
      ContDiff ℝ 3 (fun p : GW.Space => auxiliaryFixedEnergyWeightJet [] n e p0 p he.2) ∧
      (∀ p : GW.Space, (auxiliaryEnergyEmbedding n e p0 he.2).comp
        (auxiliaryFixedEnergyWeightJet [] n e p0 p he.2) = auxiliaryPhysicalFreeInverse n e p he.2) ∧
      (∀ alpha : Fin 3 → ℕ, (∑ i, alpha i) ≤ 3 → ∀ p : Fin 3 → ℝ,
        ‖p0-(EuclideanSpace.equiv (Fin 3) ℝ).symm p‖ ≤ 1 →
        ‖coordinateMultiPartial alpha
          (fun q => auxiliaryFixedEnergyWeightJet [] n e p0 ((EuclideanSpace.equiv (Fin 3) ℝ).symm q) he.2) p‖ ≤
          2*scalarDerivativeCoefficientBound (∑ i, alpha i))) := by
  refine ⟨auxiliaryPhysicalFreeInverse_contDiff n e he.2,?_,?_⟩
  · intro alpha _ p
    exact auxiliaryPhysicalFreeInverse_multiPartial_norm_le alpha n e he.2 p
  · intro p0
    refine ⟨auxiliaryFixedEnergyWeightJet_zero_contDiff n e p0 he.2,?_,?_⟩
    · intro p
      exact auxiliaryFixedEnergyWeightJet_zero_physical n e p0 p he.2
    · intro alpha _ p hp
      exact auxiliaryFixedEnergyWeightJet_zero_multiPartial_norm_le alpha n e p0 he.2 p hp

end Froehlich
