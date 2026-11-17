import Froehlich.Nodes.RS02InteractionSmooth
import Froehlich.Nodes.CA01InverseFamily
import Froehlich.Nodes.CA02PhysicalRegularity
import Froehlich.Nodes.RS01PhysicalResolvent

set_option autoImplicit false

/-! Real norm regularity of the actual chosen normalized inverse. -/
noncomputable section
open Filter
open scoped Topology
namespace Froehlich
open scoped BoundedEndReal
local instance rs02InverseSmoothHighNormedGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n) :=
  Submodule.normedAddCommGroup (HighSectorSpace n)
local instance rs02InverseSmoothEndNormedGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance rs02InverseSmoothEndRealNormedSpace (n : ℕ) : NormedSpace ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  (BoundedEndReal.realNormedAlgebra (E := HighSectorSpace n)).toNormedSpace
local instance rs02InverseSmoothEndRealBoundedSMul (n : ℕ) : IsBoundedSMul ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  NormedSpace.toIsBoundedSMul
local instance rs02InverseSmoothEndRealContinuousSMul (n : ℕ) : ContinuousSMul ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  IsBoundedSMul.continuousSMul

theorem auxiliaryNormalizedOperator_contDiff (g : ℝ) (n : ℕ) (e : ℝ)
    (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) :
    ContDiff ℝ 3 (fun p : GW.Space => auxiliaryNormalizedOperator g n e p he.2) := by
  exact contDiff_const.add (auxiliaryInteractionOperator_contDiff g n e hn he)

theorem auxiliaryNormalizedInverse_contDiff (g : ℝ) (n : ℕ) (e : ℝ)
    (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant*|g| ≤ 1/2) :
    ContDiff ℝ 3 (fun p : GW.Space => auxiliaryNormalizedInverse g n e p he.2 hg hsmall) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  apply actualInverseFamily_contDiffAt
    (fun q => auxiliaryNormalizedOperator g n e q he.2)
    (fun q => auxiliaryNormalizedInverse g n e q he.2 hg hsmall) p 3
    (auxiliaryNormalizedOperator_contDiff g n e hn he).contDiffAt
  exact Filter.Eventually.of_forall (fun q =>
    ⟨auxiliaryNormalizedInverse_right g n e q he.2 hg hsmall,
     auxiliaryNormalizedInverse_left g n e q he.2 hg hsmall⟩)

theorem auxiliaryResolvent_contDiff (g : ℝ) (n : ℕ) (e : ℝ)
    (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant*|g| ≤ 1/2) :
    ContDiff ℝ 3 (fun p : GW.Space => auxiliaryResolvent n e p he g hg hsmall) := by
  let B := ContinuousLinearMap.mul ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n)
  have hG : ContDiff ℝ 3 (fun p : GW.Space => auxiliaryPhysicalFreeInverse n e p he.2) := by
    simpa only [] using! auxiliaryPhysicalFreeInverse_contDiff n e he.2
  have hQ : ContDiff ℝ 3 (fun p : GW.Space => auxiliaryNormalizedInverse g n e p he.2 hg hsmall) :=
    auxiliaryNormalizedInverse_contDiff g n e hn he hg hsmall
  have hI : ContDiff ℝ 3 (fun p : GW.Space => B
      (auxiliaryNormalizedInverse g n e p he.2 hg hsmall) (auxiliaryPhysicalFreeInverse n e p he.2)) := by
    simpa only [Function.comp_apply] using! (B.contDiff.comp hQ).clm_apply hG
  have hO := (B.contDiff.comp hG).clm_apply hI
  simpa only [Function.comp_apply,B,ContinuousLinearMap.mul_apply',auxiliaryResolvent] using! hO

end Froehlich
