import Froehlich.Nodes.RS02SandwichReal
import Froehlich.Nodes.RS02RealActionTopology
import Froehlich.Nodes.RS02InteractionJets
import Froehlich.Nodes.CA02FixedEnergyRegularity

/-! The actual singular interaction is differentiated in a fixed energy space. -/
noncomputable section
namespace Froehlich
open scoped InnerProductSpace BoundedEndReal
local instance rs02InteractionSmoothHighNormedGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n) :=
  Submodule.normedAddCommGroup (HighSectorSpace n)
local instance rs02InteractionSmoothEndNormedGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance rs02InteractionSmoothEndRealNormedSpace (n : ℕ) : NormedSpace ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  (BoundedEndReal.realNormedAlgebra (E := HighSectorSpace n)).toNormedSpace
local instance rs02InteractionSmoothEndRealBoundedSMul (n : ℕ) : IsBoundedSMul ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  NormedSpace.toIsBoundedSMul
local instance rs02InteractionSmoothEndRealContinuousSMul (n : ℕ) : ContinuousSMul ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  IsBoundedSMul.continuousSMul

local instance rs02InteractionSmoothEnergyNormedGroup (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) :
    NormedAddCommGroup (AuxiliaryEnergySpace n e p0 he) :=
  Submodule.normedAddCommGroup (AuxiliaryEnergySpace n e p0 he)
local instance rs02InteractionSmoothMapNormedGroup (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) :
    NormedAddCommGroup (HighSectorSpace n →L[ℂ] AuxiliaryEnergySpace n e p0 he) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance rs02InteractionSmoothMapRealNormedSpace (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) :
    NormedSpace ℝ (HighSectorSpace n →L[ℂ] AuxiliaryEnergySpace n e p0 he) :=
  NormedSpace.restrictScalars ℝ ℂ _
local instance rs02InteractionSmoothMapBoundedSMul (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) :
    IsBoundedSMul ℝ (HighSectorSpace n →L[ℂ] AuxiliaryEnergySpace n e p0 he) :=
  NormedSpace.toIsBoundedSMul
local instance rs02InteractionSmoothMapContinuousSMul (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) :
    ContinuousSMul ℝ (HighSectorSpace n →L[ℂ] AuxiliaryEnergySpace n e p0 he) :=
  IsBoundedSMul.continuousSMul

local instance rs02InteractionSmoothNestedContinuous (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) :
    ContinuousSMul ℝ ((HighSectorSpace n →L[ℂ] AuxiliaryEnergySpace n e p0 he) →L[ℂ]
      (HighSectorSpace n →L[ℂ] HighSectorSpace n)) := by
  exact realContinuousSMulOfComplex
    (E := (HighSectorSpace n →L[ℂ] AuxiliaryEnergySpace n e p0 he) →L[ℂ]
      (HighSectorSpace n →L[ℂ] HighSectorSpace n))

def auxiliaryFixedInteractionForm (g : ℝ) (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) :
    GW.Analysis.BoundedForm (AuxiliaryEnergySpace n e p0 he) :=
  boundedFormPullback (singularInteraction g (-p0))
    (auxiliaryToEnergy n e p0 he) (auxiliaryToEnergy n e p0 he)

theorem auxiliaryInteraction_fixed_sandwich (g : ℝ) (n : ℕ) (e : ℝ)
    (p0 p : GW.Space) (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) :
    auxiliaryInteractionOperator g n e p he.2 =
      formSandwichReal (auxiliaryFixedInteractionForm g n e p0 he.2)
        (auxiliaryFixedEnergyWeightJet [] n e p0 p he.2)
        (auxiliaryFixedEnergyWeightJet [] n e p0 p he.2) := by
  apply formRepresentative_unique
  intro w u
  change singularInteraction g (-p0)
    (auxiliaryOriginalWeightJet [] n e p0 p he.2 w)
    (auxiliaryOriginalWeightJet [] n e p0 p he.2 u) = _
  have h := auxiliaryInteractionJetPair_spec g [] [] n e p0 p hn he w u
  simpa only [auxiliaryInteractionJetPair,auxiliaryRelativeWeightJet_nil,
    ContinuousLinearMap.adjoint_one,ContinuousLinearMap.comp_apply,ContinuousLinearMap.one_apply] using h

theorem auxiliaryInteractionOperator_contDiff (g : ℝ) (n : ℕ) (e : ℝ)
    (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) :
    ContDiff ℝ 3 (fun p : GW.Space => auxiliaryInteractionOperator g n e p he.2) := by
  let p0 : GW.Space := 0
  have hf := auxiliaryFixedEnergyWeightJet_zero_contDiff n e p0 he.2
  have h := formSandwichReal_contDiff
    (auxiliaryFixedInteractionForm g n e p0 he.2) 3
    (fun p : GW.Space => auxiliaryFixedEnergyWeightJet [] n e p0 p he.2)
    (fun p : GW.Space => auxiliaryFixedEnergyWeightJet [] n e p0 p he.2) hf hf
  have hEq : (fun p : GW.Space => auxiliaryInteractionOperator g n e p he.2) =
      (fun p => formSandwichReal (auxiliaryFixedInteractionForm g n e p0 he.2)
        (auxiliaryFixedEnergyWeightJet [] n e p0 p he.2)
        (auxiliaryFixedEnergyWeightJet [] n e p0 p he.2)) := by
    funext p
    exact auxiliaryInteraction_fixed_sandwich g n e p0 p hn he
  rw [hEq]
  exact h

end Froehlich
