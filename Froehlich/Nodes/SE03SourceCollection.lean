import Froehlich.Nodes.SE02
import Froehlich.Nodes.OP02SourcePairings

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2)

/-- Collecting the true lambda source uses only division by 1+e. -/
theorem se03_right_source_collected (w : OneParticleEnergySpace 0) :
    se02RightLoad e he g hg hs w-((e/(1+e) : ℝ) : ℂ)*
      (starRingEnd ℂ) (translatedLinearSource g 0 w) =
      (kernelConstant e he g hg hs 0 : ℂ)*(starRingEnd ℂ) (translatedLinearSource g 0 w)+
        ⟪oneParticleRadialMap w,thresholdKernelSourceVector e he g hg hs 0 (by simp)⟫_ℂ := by
  let A : ℂ := ((kernelConstant e he g hg hs 0+e/(1+e) : ℝ) : ℂ)
  let base := fun q : GW.Space => (starRingEnd ℂ) (oneParticleEnergyEmbedding 0 w q)*(fiberFormFactor g q : ℂ)
  let psi := fun q : GW.Space => base q*(kernelPsi e he g hg hs 0 q : ℂ)
  have ht : 1+e ≠ 0 := by linarith [he.1]
  have hscalar (q : GW.Space) : (1-(groundSourceLambda e he g hg hs q : ℂ)) =
      A+(kernelPsi e he g hg hs 0 q : ℂ) := by
    have hreal : 1-groundSourceLambda e he g hg hs q =
        kernelConstant e he g hg hs 0+e/(1+e)+kernelPsi e he g hg hs 0 q := by
      rw [kernelConstant_zero_lambda,kernelPsi_zero_lambda]
      field_simp [ht]
      <;> ring
    simpa only [A,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_add] using
      congrArg (fun r : ℝ => (r : ℂ)) hreal
  have hb := translatedLinearSource_star_integral g 0 w
  have hp := radial_inner_kernelSource_integral e he g hg hs 0 (by simp) w
  have hbi : Integrable base volume := by simpa only [base,add_zero] using hb.1
  have hpi : Integrable psi volume := by simpa only [psi,base,add_zero] using hp.1
  have hbe : (starRingEnd ℂ) (translatedLinearSource g 0 w) = ∫ q : GW.Space,base q := by
    simpa only [base,add_zero] using hb.2
  have hpe : ⟪oneParticleRadialMap w,thresholdKernelSourceVector e he g hg hs 0 (by simp)⟫_ℂ =
      ∫ q : GW.Space,psi q := by simpa only [psi,base,add_zero] using hp.2
  have hright := (se02_right_load_integral e he g hg hs w).2
  have heq : se02RightLoad e he g hg hs w = A*(∫ q : GW.Space,base q)+(∫ q : GW.Space,psi q) := by
    calc
      _ = ∫ q : GW.Space,A*base q+psi q := hright.trans (integral_congr_ae
        (Filter.Eventually.of_forall (fun q => by
          change base q*(1-(groundSourceLambda e he g hg hs q : ℂ)) = _
          rw [hscalar]
          dsimp only [psi]
          ring)))
      _ = _ := by rw [integral_add (hbi.const_mul A) hpi,integral_const_mul]
  rw [heq,←hbe,←hpe]
  simp only [A,Complex.ofReal_add]
  ring

end Froehlich
