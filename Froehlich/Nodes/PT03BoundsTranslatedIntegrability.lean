import Froehlich.Nodes.PT03KernelMeasurability
import Froehlich.Nodes.PT03BoundsKernels
import Froehlich.Nodes.TR01
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

/-! Absolute convergence of the final translated C kernel on the actual
zero-momentum one-particle energy domain. -/
noncomputable section
open MeasureTheory
namespace Froehlich

theorem translatedSource_double_majorant_integrable (g : ℝ) (P : GW.Space)
    (f h : OneParticleEnergySpace 0) (C : ℝ) :
    Integrable (fun x : GW.Space × GW.Space => C *
      (‖(starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f x.1)*(fiberFormFactor g (x.1+P) : ℂ)‖ *
       ‖(starRingEnd ℂ) (oneParticleEnergyEmbedding 0 h x.2)*(fiberFormFactor g (x.2+P) : ℂ)‖))
      (volume.prod volume) :=
  (((translatedFiberSourceLoad_integrable g P f).norm).mul_prod
    (translatedFiberSourceLoad_integrable g P h).norm).const_mul C

theorem translatedThresholdKernelC_form_integrable (e : ℝ)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P : GW.Space) (hP : ‖P‖ ≤ 1/4)
    (f h : OneParticleEnergySpace 0) :
    Integrable (fun x : GW.Space × GW.Space =>
      (starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f x.1)*(fiberFormFactor g (x.1+P) : ℂ)*
        thresholdKernelC e he g hg hs P x.1 x.2*(fiberFormFactor g (x.2+P) : ℂ)*
          oneParticleEnergyEmbedding 0 h x.2) (volume.prod volume) := by
  obtain ⟨C,hC,hBound⟩ := thresholdKernels_uniform_bound
  let T : GW.Space × GW.Space → GW.Space × (GW.Space × GW.Space) := fun x => (P,x)
  have hT : Measurable T := measurable_const.prodMk measurable_id
  have hCM := (thresholdKernelC_measurable e he g hg hs).comp hT
  have hCm : Measurable (fun x : GW.Space × GW.Space => thresholdKernelC e he g hg hs P x.1 x.2) := by
    simpa only [T,Function.comp_def] using hCM
  have hv : AEStronglyMeasurable (fun q : GW.Space => (fiberFormFactor g (q+P) : ℂ)) volume :=
    (Complex.continuous_ofReal.measurable.comp
      ((fiberFormFactor_measurable g).comp (measurable_id.add_const P))).aestronglyMeasurable
  have hm : AEStronglyMeasurable (fun x : GW.Space × GW.Space =>
      (starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f x.1)*(fiberFormFactor g (x.1+P) : ℂ)*
        thresholdKernelC e he g hg hs P x.1 x.2*(fiberFormFactor g (x.2+P) : ℂ)*
          oneParticleEnergyEmbedding 0 h x.2) (volume.prod volume) :=
    (((((Complex.conjCLE.continuous.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable (oneParticleEnergyEmbedding 0 f))).comp_fst).mul hv.comp_fst).mul
        hCm.aestronglyMeasurable).mul hv.comp_snd).mul
          (Lp.aestronglyMeasurable (oneParticleEnergyEmbedding 0 h)).comp_snd
  apply (translatedSource_double_majorant_integrable g P f h C).mono' hm
  exact Filter.Eventually.of_forall (fun x => by
    simp only [norm_mul,RCLike.norm_conj]
    have hc := (hBound g e he hg hs P x.1 x.2 hP).2.1
    calc
      _ = (‖oneParticleEnergyEmbedding 0 f x.1‖*‖(fiberFormFactor g (x.1+P) : ℂ)‖)*
          (‖oneParticleEnergyEmbedding 0 h x.2‖*‖(fiberFormFactor g (x.2+P) : ℂ)‖)*
            ‖thresholdKernelC e he g hg hs P x.1 x.2‖ := by ring
      _ ≤ (‖oneParticleEnergyEmbedding 0 f x.1‖*‖(fiberFormFactor g (x.1+P) : ℂ)‖)*
          (‖oneParticleEnergyEmbedding 0 h x.2‖*‖(fiberFormFactor g (x.2+P) : ℂ)‖)*C :=
        mul_le_mul_of_nonneg_left hc (by positivity)
      _ = _ := by ring)

end Froehlich
