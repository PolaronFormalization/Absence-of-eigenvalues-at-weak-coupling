import Froehlich.Nodes.WE02
import Froehlich.Nodes.SY01Annihilation

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace Froehlich

/-- Native measure-preserving reflection on the unchanged real L-infinity quotient. -/
def realLinftyReflection : Lp ℝ ⊤ (volume : Measure GW.Space) →ₗᵢ[ℝ] Lp ℝ ⊤ (volume : Measure GW.Space) :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun q : GW.Space => -q) space_negation_preserving

theorem realLinftyReflection_ae (f : Lp ℝ ⊤ (volume : Measure GW.Space)) :
    realLinftyReflection f =ᵐ[volume] (fun q => f (-q)) :=
  Lp.coeFn_compMeasurePreserving f space_negation_preserving

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2)

theorem normalizedWeightedKernel_zero_reflection (q r : GW.Space) :
    normalizedWeightedKernel e he g hg hs 0 (-q) (-r) = normalizedWeightedKernel e he g hg hs 0 q r := by
  have hF := remainderKernel_reflection e he g hg hs 0 q r
  simp only [neg_zero] at hF
  simp only [normalizedWeightedKernel,neg_eq_zero,omega,norm_neg,muDensity,add_zero,hF]

theorem normalizedKernelPsi_zero_reflection (q : GW.Space) :
    normalizedKernelPsi e he g hg hs 0 (-q) = normalizedKernelPsi e he g hg hs 0 q := by
  simp only [normalizedKernelPsi,neg_eq_zero,omega,norm_neg,
    kernelPsi_zeroMomentum_even e he g hg hs q]

theorem normalizedWeightedIntegral_zero_reflection
    (f : Lp ℝ ⊤ (volume : Measure GW.Space)) (q : GW.Space) :
    normalizedWeightedIntegral e he g hg hs 0 (realLinftyReflection f) q =
      normalizedWeightedIntegral e he g hg hs 0 f (-q) := by
  unfold normalizedWeightedIntegral
  calc
    _ = ∫ r,normalizedWeightedKernel e he g hg hs 0 q r*f (-r) := by
      apply integral_congr_ae
      filter_upwards [realLinftyReflection_ae f] with r hr
      rw [hr]
    _ = ∫ r,normalizedWeightedKernel e he g hg hs 0 q (-r)*f r := by
      have h := space_negation_preserving.integral_comp (MeasurableEquiv.neg GW.Space).measurableEmbedding
        (fun r => normalizedWeightedKernel e he g hg hs 0 q r*f (-r))
      simpa only [neg_neg] using h.symm
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun r => by
        have h := normalizedWeightedKernel_zero_reflection e he g hg hs (-q) r
        simp only [neg_neg] at h
        exact congrArg (fun z : ℝ => z*f r) h)

theorem weightedKernelOperator_zero_reflection (f : Lp ℝ ⊤ (volume : Measure GW.Space)) :
    weightedKernelOperator e he g hg hs 0 (by simp) (realLinftyReflection f) =
      realLinftyReflection (weightedKernelOperator e he g hg hs 0 (by simp) f) := by
  have hneg := space_negation_preserving.quasiMeasurePreserving.ae
    (weightedKernelOperator_ae e he g hg hs 0 (by simp) f)
  apply Lp.ext
  filter_upwards [weightedKernelOperator_ae e he g hg hs 0 (by simp) (realLinftyReflection f),
    realLinftyReflection_ae (weightedKernelOperator e he g hg hs 0 (by simp) f),hneg] with q hl hr hneg
  rw [hl,hr,hneg]
  exact normalizedWeightedIntegral_zero_reflection e he g hg hs f q

theorem weightedKernelSource_zero_reflection :
    realLinftyReflection (weightedKernelSource e he g hg hs 0 (by simp)) =
      weightedKernelSource e he g hg hs 0 (by simp) := by
  have hneg := space_negation_preserving.quasiMeasurePreserving.ae
    (weightedKernelSource_ae e he g hg hs 0 (by simp))
  apply Lp.ext
  filter_upwards [realLinftyReflection_ae (weightedKernelSource e he g hg hs 0 (by simp)),
    weightedKernelSource_ae e he g hg hs 0 (by simp),hneg] with q hr hs0 hneg
  rw [hr,hneg,hs0,normalizedKernelPsi_zero_reflection]

end Froehlich
