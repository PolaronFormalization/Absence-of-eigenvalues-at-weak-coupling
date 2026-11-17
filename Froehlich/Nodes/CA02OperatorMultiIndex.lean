import Froehlich.Nodes.CA02PhysicalRegularity
import Froehlich.Nodes.CA02FixedEnergyRegularity
import Froehlich.Nodes.CA02FixedEnergyPhysical
import Froehlich.Nodes.CA02CanonicalExpansion

set_option autoImplicit false

/-! Canonical mixed derivatives are the genuine operator jets, in the exact
ordered coordinate convention. No mixed-derivative commutation is assumed. -/
noncomputable section
namespace Froehlich
open scoped BoundedEndReal
local instance ca02OperatorMultiIndexHighNormedGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n) :=
  Submodule.normedAddCommGroup (HighSectorSpace n)
local instance ca02OperatorMultiIndexEndNormedGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance ca02OperatorMultiIndexEndRealNormedSpace (n : ℕ) : NormedSpace ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  (BoundedEndReal.realNormedAlgebra (E := HighSectorSpace n)).toNormedSpace
local instance ca02OperatorMultiIndexEndRealBoundedSMul (n : ℕ) : IsBoundedSMul ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  NormedSpace.toIsBoundedSMul
local instance ca02OperatorMultiIndexEndRealContinuousSMul (n : ℕ) : ContinuousSMul ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  IsBoundedSMul.continuousSMul

local instance ca02OperatorMultiIndexEnergyNormedGroup (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) :
    NormedAddCommGroup (AuxiliaryEnergySpace n e p0 he) :=
  Submodule.normedAddCommGroup (AuxiliaryEnergySpace n e p0 he)
local instance ca02OperatorMultiIndexEnergyMapNormedGroup (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) :
    NormedAddCommGroup (HighSectorSpace n →L[ℂ] AuxiliaryEnergySpace n e p0 he) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance ca02OperatorMultiIndexEnergyMapRealNormedSpace (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) :
    NormedSpace ℝ (HighSectorSpace n →L[ℂ] AuxiliaryEnergySpace n e p0 he) :=
  NormedSpace.restrictScalars ℝ ℂ _
local instance ca02OperatorMultiIndexEnergyMapRealBoundedSMul (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) :
    IsBoundedSMul ℝ (HighSectorSpace n →L[ℂ] AuxiliaryEnergySpace n e p0 he) :=
  NormedSpace.toIsBoundedSMul
local instance ca02OperatorMultiIndexEnergyMapRealContinuousSMul (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) :
    ContinuousSMul ℝ (HighSectorSpace n →L[ℂ] AuxiliaryEnergySpace n e p0 he) :=
  IsBoundedSMul.continuousSMul

private theorem coordinateUnitBlocks_of_nativeJets {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (J : List (Fin 3) → (Fin 3 → ℝ) → V)
    (h : ∀ is p i, HasDerivAt (fun t : ℝ => J is (Function.update p i t)) (J (i::is) p) (p i))
    (is : List (Fin 3)) :
    coordinateBlocksPartial (is.map (fun i => (i,1))) (J []) = J is := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [List.map_cons,coordinateBlocksPartial]
    rw [ih]
    change coordinatePartial i (J is) = J (i::is)
    funext p
    exact (h is p i).deriv

theorem auxiliaryPhysicalFreeInverse_multiPartial (alpha : Fin 3 → ℕ) (n : ℕ)
    (e : ℝ) (he : e ≤ 0) (p : Fin 3 → ℝ) :
    coordinateMultiPartial alpha
      (fun q => auxiliaryPhysicalFreeInverse n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm q) he) p =
    auxiliaryPhysicalWeightJet (canonicalMultiIndexCoordinates alpha) n e
      ((EuclideanSpace.equiv (Fin 3) ℝ).symm p) he := by
  change coordinateMultiPartial alpha (auxiliaryPhysicalWeightJetChart n e he []) p = _
  rw [coordinateMultiPartial_eq_unitBlocks]
  have h := coordinateUnitBlocks_of_nativeJets (auxiliaryPhysicalWeightJetChart n e he)
    (fun is p i => auxiliaryPhysicalWeightJetChart_hasDerivAt_update is n e he p i)
    (canonicalMultiIndexCoordinates alpha)
  exact congrFun h p

theorem auxiliaryPhysicalFreeInverse_multiPartial_norm_le (alpha : Fin 3 → ℕ) (n : ℕ)
    (e : ℝ) (he : e ≤ 0) (p : Fin 3 → ℝ) :
    ‖coordinateMultiPartial alpha
      (fun q => auxiliaryPhysicalFreeInverse n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm q) he) p‖ ≤
      scalarDerivativeCoefficientBound (∑ i, alpha i) := by
  rw [auxiliaryPhysicalFreeInverse_multiPartial]
  simpa only [canonicalMultiIndexCoordinates_length] using!
    auxiliaryPhysicalWeightJet_norm_le (canonicalMultiIndexCoordinates alpha) n e
      ((EuclideanSpace.equiv (Fin 3) ℝ).symm p) he

theorem auxiliaryFixedEnergyWeightJet_zero_multiPartial (alpha : Fin 3 → ℕ) (n : ℕ)
    (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) (p : Fin 3 → ℝ) :
    coordinateMultiPartial alpha
      (fun q => auxiliaryFixedEnergyWeightJet [] n e p0 ((EuclideanSpace.equiv (Fin 3) ℝ).symm q) he) p =
    auxiliaryFixedEnergyWeightJet (canonicalMultiIndexCoordinates alpha) n e p0
      ((EuclideanSpace.equiv (Fin 3) ℝ).symm p) he := by
  change coordinateMultiPartial alpha (auxiliaryFixedEnergyWeightJetChart n e p0 he []) p = _
  rw [coordinateMultiPartial_eq_unitBlocks]
  have h := coordinateUnitBlocks_of_nativeJets (auxiliaryFixedEnergyWeightJetChart n e p0 he)
    (fun is p i => auxiliaryFixedEnergyWeightJetChart_hasDerivAt_update is n e p0 he p i)
    (canonicalMultiIndexCoordinates alpha)
  exact congrFun h p

theorem auxiliaryFixedEnergyWeightJet_zero_multiPartial_norm_le (alpha : Fin 3 → ℕ) (n : ℕ)
    (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) (p : Fin 3 → ℝ)
    (hp : ‖p0-(EuclideanSpace.equiv (Fin 3) ℝ).symm p‖ ≤ 1) :
    ‖coordinateMultiPartial alpha
      (fun q => auxiliaryFixedEnergyWeightJet [] n e p0 ((EuclideanSpace.equiv (Fin 3) ℝ).symm q) he) p‖ ≤
      2*scalarDerivativeCoefficientBound (∑ i, alpha i) := by
  rw [auxiliaryFixedEnergyWeightJet_zero_multiPartial]
  simpa only [canonicalMultiIndexCoordinates_length] using!
    auxiliaryFixedEnergyWeightJet_local_norm_le (canonicalMultiIndexCoordinates alpha) n e p0
      ((EuclideanSpace.equiv (Fin 3) ℝ).symm p) he hp

end Froehlich
