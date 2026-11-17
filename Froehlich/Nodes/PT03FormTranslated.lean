import Froehlich.Nodes.PT03FormUntranslated
import Froehlich.Nodes.PT03BoundsTranslation
import Froehlich.Nodes.PT03BoundsScalarTranslation

set_option autoImplicit false

/-! PT03's full translated complex form identity and absolute convergence,
on the complete actual zero-momentum one-particle energy space. -/
noncomputable section
open MeasureTheory
namespace Froehlich

theorem translatedThresholdForm_kernel_formula (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (hquarter : |g| ≤ 1/4) (heLower : -sectorEnergyConstant*|g|^2 ≤ e)
    (hquadratic : sectorQuadraticConstant*|g|^2 ≤ 1/8) (P : GW.Space) (hP : ‖P‖ ≤ 1/4)
    (f h : OneParticleEnergySpace 0) :
    Integrable (fun q : GW.Space => (starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f q)*
      ((‖q‖^2+auxiliarySelfEnergy e q he g hg hs-e : ℝ) : ℂ)*oneParticleEnergyEmbedding 0 h q) volume ∧
    Integrable (fun x : GW.Space × GW.Space =>
      (starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f x.1)*(fiberFormFactor g (x.1+P) : ℂ)*
        thresholdKernelC e he g hg hs P x.1 x.2*(fiberFormFactor g (x.2+P) : ℂ)*
          oneParticleEnergyEmbedding 0 h x.2) (volume.prod volume) ∧
    translatedThresholdForm e he g hquarter heLower hquadratic P hP f h =
      (∫ q : GW.Space, (starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f q)*
        ((‖q‖^2+auxiliarySelfEnergy e q he g hg hs-e : ℝ) : ℂ)*oneParticleEnergyEmbedding 0 h q) +
      ∫ x : GW.Space × GW.Space,
        (starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f x.1)*(fiberFormFactor g (x.1+P) : ℂ)*
          thresholdKernelC e he g hg hs P x.1 x.2*(fiberFormFactor g (x.2+P) : ℂ)*
            oneParticleEnergyEmbedding 0 h x.2 ∂volume.prod volume := by
  refine ⟨translatedThresholdFullDiagonal_integrable e he g hg hs f h,
    translatedThresholdKernelC_form_integrable e he g hg hs P hP f h,?_⟩
  unfold translatedThresholdForm
  rw [untranslatedThresholdForm_kernel_formula e he g hg hs hquarter heLower hquadratic P hP,
    thresholdScalar_translation_integral e he g hg hs P f h,
    thresholdKernelC_translation_integral e he g hg hs P hP f h]

end Froehlich
