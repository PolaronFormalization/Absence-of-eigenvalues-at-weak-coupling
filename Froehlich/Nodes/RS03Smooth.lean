import Froehlich.Nodes.RS03StaticBounded
import Froehlich.Nodes.RS02SourceDerivativesComposition
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false

/-! Actual real C2 regularity of the bounded self-energy expression. -/
noncomputable section
namespace Froehlich
open scoped InnerProductSpace
local instance rs03SmoothHighGroup : NormedAddCommGroup (HighSectorSpace 1) :=
  Submodule.normedAddCommGroup (HighSectorSpace 1)
local instance rs03SmoothHighReal : NormedSpace ℝ (HighSectorSpace 1) :=
  NormedSpace.restrictScalars ℝ ℂ _
local instance rs03SmoothHighModule : Module ℝ (HighSectorSpace 1) := rs03SmoothHighReal.toModule
local instance rs03SmoothHighBounded : IsBoundedSMul ℝ (HighSectorSpace 1) := NormedSpace.toIsBoundedSMul
local instance rs03SmoothHighContinuous : ContinuousSMul ℝ (HighSectorSpace 1) := IsBoundedSMul.continuousSMul

theorem auxiliarySelfEnergy_contDiff (g e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2) :
    ContDiff ℝ 2 (fun p : GW.Space => auxiliarySelfEnergy e p he g hg hs) := by
  have hz : ContDiff ℝ 3 (fun p : GW.Space => auxiliaryNormalizedSource g e p he.2) := by
    simpa only [] using! auxiliaryNormalizedSource_contDiff g e he
  have hQz : ContDiff ℝ 3 (fun p : GW.Space => auxiliaryNormalizedInverse g 1 e p he.2 hg hs
      (auxiliaryNormalizedSource g e p he.2)) := by
    simpa only [] using! auxiliaryNormalizedInverse_source_contDiff g e he hg hs
  have hi : ContDiff ℝ 3 (fun p : GW.Space => ⟪auxiliaryNormalizedSource g e p he.2,
      auxiliaryNormalizedInverse g 1 e p he.2 hg hs (auxiliaryNormalizedSource g e p he.2)⟫_ℂ) := by
    simpa only [] using! hz.inner ℂ hQz
  have hr := (Complex.reCLM.contDiff.comp hi).neg
  have heq : (fun p : GW.Space => auxiliarySelfEnergy e p he g hg hs) =
      (fun p : GW.Space => -(⟪auxiliaryNormalizedSource g e p he.2,
        auxiliaryNormalizedInverse g 1 e p he.2 hg hs (auxiliaryNormalizedSource g e p he.2)⟫_ℂ).re) := by
    funext p
    exact auxiliarySelfEnergy_bounded_formula e p he g hg hs
  rw [heq]
  simpa only [Function.comp_apply] using! hr.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)

end Froehlich
