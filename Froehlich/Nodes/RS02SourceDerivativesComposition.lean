import Froehlich.Nodes.RS02InverseSmooth
import Froehlich.Nodes.RS02SourceSmoothC3
import Froehlich.Nodes.RS02SourceEnergy

set_option autoImplicit false

/-! Genuine full-Fock Hilbert-norm C3 regularity of the actual source
solution h=GQz. Complex-linear operators are viewed as real-linear ONLY
through the native restriction isometry for real-parameter calculus. -/
noncomputable section
namespace Froehlich
open scoped BoundedEndReal
local instance rs02SourceCompositionHighGroup : NormedAddCommGroup (HighSectorSpace 1) :=
  Submodule.normedAddCommGroup (HighSectorSpace 1)
local instance rs02SourceCompositionHighReal : NormedSpace ℝ (HighSectorSpace 1) :=
  NormedSpace.restrictScalars ℝ ℂ _
local instance rs02SourceCompositionHighModule : Module ℝ (HighSectorSpace 1) :=
  rs02SourceCompositionHighReal.toModule
local instance rs02SourceCompositionFockReal : NormedSpace ℝ GW.Fock.Carrier :=
  NormedSpace.restrictScalars ℝ ℂ _
local instance rs02SourceCompositionHighBounded : IsBoundedSMul ℝ (HighSectorSpace 1) :=
  NormedSpace.toIsBoundedSMul
local instance rs02SourceCompositionHighContinuous : ContinuousSMul ℝ (HighSectorSpace 1) :=
  IsBoundedSMul.continuousSMul
local instance rs02SourceCompositionFockBounded : IsBoundedSMul ℝ GW.Fock.Carrier :=
  NormedSpace.toIsBoundedSMul
local instance rs02SourceCompositionFockContinuous : ContinuousSMul ℝ GW.Fock.Carrier :=
  IsBoundedSMul.continuousSMul
local instance rs02SourceCompositionEndGroup : NormedAddCommGroup (HighSectorSpace 1 →L[ℂ] HighSectorSpace 1) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance rs02SourceCompositionEndReal : NormedSpace ℝ (HighSectorSpace 1 →L[ℂ] HighSectorSpace 1) :=
  (BoundedEndReal.realNormedAlgebra (E := HighSectorSpace 1)).toNormedSpace
local instance rs02SourceCompositionEndBounded : IsBoundedSMul ℝ (HighSectorSpace 1 →L[ℂ] HighSectorSpace 1) :=
  NormedSpace.toIsBoundedSMul
local instance rs02SourceCompositionEndContinuous : ContinuousSMul ℝ (HighSectorSpace 1 →L[ℂ] HighSectorSpace 1) :=
  IsBoundedSMul.continuousSMul

local instance rs02SourceCompositionRealEndGroup : NormedAddCommGroup (HighSectorSpace 1 →L[ℝ] HighSectorSpace 1) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance rs02SourceCompositionHighSelfScalarComm : SMulCommClass ℝ ℝ (HighSectorSpace 1) where
  smul_comm r s x := by
    apply Subtype.ext
    change (r : ℂ) • ((s : ℂ) • (x : GW.Fock.Carrier)) =
      (s : ℂ) • ((r : ℂ) • (x : GW.Fock.Carrier))
    rw [smul_smul, smul_smul, mul_comm]
local instance rs02SourceCompositionRealEndSpace : NormedSpace ℝ (HighSectorSpace 1 →L[ℝ] HighSectorSpace 1) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := HighSectorSpace 1) (F := HighSectorSpace 1) (σ₁₂ := RingHom.id ℝ)
local instance rs02SourceCompositionRealEndBounded : IsBoundedSMul ℝ (HighSectorSpace 1 →L[ℝ] HighSectorSpace 1) :=
  NormedSpace.toIsBoundedSMul
local instance rs02SourceCompositionRealEndContinuous : ContinuousSMul ℝ (HighSectorSpace 1 →L[ℝ] HighSectorSpace 1) :=
  IsBoundedSMul.continuousSMul

theorem auxiliaryNormalizedInverse_source_contDiff (g e : ℝ)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (hg : |g| ≤ 1)
    (hsmall : auxiliaryResolventConstant*|g| ≤ 1/2) :
    ContDiff ℝ 3 (fun p : GW.Space => auxiliaryNormalizedInverse g 1 e p he.2 hg hsmall
      (auxiliaryNormalizedSource g e p he.2)) := by
  let V : (HighSectorSpace 1 →L[ℂ] HighSectorSpace 1) →L[ℝ]
      (HighSectorSpace 1 →L[ℝ] HighSectorSpace 1) :=
    (ContinuousLinearMap.restrictScalarsIsometry ℂ (HighSectorSpace 1) (HighSectorSpace 1) ℝ ℝ).toContinuousLinearMap
  have hQc : ContDiff ℝ 3 (fun p : GW.Space => auxiliaryNormalizedInverse g 1 e p he.2 hg hsmall) := by
    simpa only [] using! auxiliaryNormalizedInverse_contDiff g 1 e (by norm_num) he hg hsmall
  have hQ : ContDiff ℝ 3 (fun p : GW.Space => V (auxiliaryNormalizedInverse g 1 e p he.2 hg hsmall)) := by
    simpa only [Function.comp_def] using! V.contDiff.comp hQc
  have hzc : ContDiff ℝ 3 (fun p : GW.Space => auxiliaryNormalizedSource g e p he.2) := by
    simpa only [] using! auxiliaryNormalizedSource_contDiff g e he
  have h := hQ.clm_apply hzc
  change ContDiff ℝ 3 (fun p : GW.Space => auxiliaryNormalizedInverse g 1 e p he.2 hg hsmall
    (auxiliaryNormalizedSource g e p he.2)) at h
  exact h

theorem auxiliaryGroundSourceVector_contDiff (g e : ℝ)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (hg : |g| ≤ 1)
    (hsmall : auxiliaryResolventConstant*|g| ≤ 1/2) :
    ContDiff ℝ 3 (fun p : GW.Space => auxiliaryGroundSourceVector e p he g hg hsmall) := by
  let V : (HighSectorSpace 1 →L[ℂ] HighSectorSpace 1) →L[ℝ]
      (HighSectorSpace 1 →L[ℝ] HighSectorSpace 1) :=
    (ContinuousLinearMap.restrictScalarsIsometry ℂ (HighSectorSpace 1) (HighSectorSpace 1) ℝ ℝ).toContinuousLinearMap
  have hGc : ContDiff ℝ 3 (fun p : GW.Space => auxiliaryPhysicalFreeInverse 1 e p he.2) := by
    simpa only [] using! auxiliaryPhysicalFreeInverse_contDiff 1 e he.2
  have hG : ContDiff ℝ 3 (fun p : GW.Space => V (auxiliaryPhysicalFreeInverse 1 e p he.2)) := by
    simpa only [Function.comp_def] using! V.contDiff.comp hGc
  have hh := hG.clm_apply (auxiliaryNormalizedInverse_source_contDiff g e he hg hsmall)
  have hfull := ((HighSectorSpace 1).subtypeL.restrictScalars ℝ).contDiff.comp hh
  have hfun : (fun p : GW.Space => auxiliaryGroundSourceVector e p he g hg hsmall) =
      (fun p : GW.Space => (auxiliaryPhysicalFreeInverse 1 e p he.2
        (auxiliaryNormalizedInverse g 1 e p he.2 hg hsmall (auxiliaryNormalizedSource g e p he.2)) : GW.Fock.Carrier)) := by
    funext p
    exact auxiliaryGroundSourceVector_formula g e p he hg hsmall
  change ContDiff ℝ 3 (fun p : GW.Space => (auxiliaryPhysicalFreeInverse 1 e p he.2
    (auxiliaryNormalizedInverse g 1 e p he.2 hg hsmall (auxiliaryNormalizedSource g e p he.2)) : GW.Fock.Carrier)) at hfull
  rw [hfun]
  exact hfull

end Froehlich
