import Froehlich.Nodes.OP02RemainderForm

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace Froehlich

theorem translatedLinearSource_star_integral (g : ℝ) (P : GW.Space) (f : OneParticleEnergySpace 0) :
    Integrable (fun q : GW.Space => (starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f q)*(fiberFormFactor g (q+P) : ℂ)) volume ∧
    (starRingEnd ℂ) (translatedLinearSource g P f) =
      ∫ q : GW.Space,(starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f q)*(fiberFormFactor g (q+P) : ℂ) := by
  refine ⟨translatedFiberSourceLoad_integrable g P f,?_⟩
  have h : (starRingEnd ℂ) (translatedLinearSource g P f) = translatedFiberSourceLoad g P f := by
    change star (star (translatedFiberSourceLoad g P f)) = translatedFiberSourceLoad g P f
    exact star_star _
  exact h.trans (translatedFiberSourceLoad_integral g P f)

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P : GW.Space) (hP : ‖P‖ ≤ 1/4)

private theorem op02_source_pairing_scalar (q : GW.Space) (hq : q ≠ 0) (z : ℂ) :
    (starRingEnd ℂ) (kernelSourceCoefficient e he g hg hs P q)*((‖q‖ : ℂ)*z) =
      (fiberFormFactor g (q+P) : ℂ)*(kernelPsi e he g hg hs P q : ℂ)*z := by
  simp only [kernelSourceCoefficient,map_mul,Complex.conj_ofReal]
  calc
    _ = ((g : ℂ)*(wDensity P q : ℂ)*(‖q‖ : ℂ))*(kernelPsi e he g hg hs P q : ℂ)*z := by ring
    _ = _ := by rw [radialWeightedSource_factor g P q hq]

private theorem op02_source_pairing_scalar_reverse (q : GW.Space) (hq : q ≠ 0) (z : ℂ) :
    (starRingEnd ℂ) ((‖q‖ : ℂ)*z)*kernelSourceCoefficient e he g hg hs P q =
      (starRingEnd ℂ) z*(fiberFormFactor g (q+P) : ℂ)*(kernelPsi e he g hg hs P q : ℂ) := by
  simp only [kernelSourceCoefficient,map_mul,Complex.conj_ofReal]
  calc
    _ = (starRingEnd ℂ) z*((g : ℂ)*(wDensity P q : ℂ)*(‖q‖ : ℂ))*(kernelPsi e he g hg hs P q : ℂ) := by ring
    _ = _ := by rw [radialWeightedSource_factor g P q hq]

theorem kernelSource_inner_radial_integral (f : OneParticleEnergySpace 0) :
    Integrable (fun q : GW.Space => (fiberFormFactor g (q+P) : ℂ)*(kernelPsi e he g hg hs P q : ℂ)*
      oneParticleEnergyEmbedding 0 f q) volume ∧
    ⟪thresholdKernelSourceVector e he g hg hs P hP,oneParticleRadialMap f⟫_ℂ =
      ∫ q : GW.Space,(fiberFormFactor g (q+P) : ℂ)*(kernelPsi e he g hg hs P q : ℂ)*
        oneParticleEnergyEmbedding 0 f q := by
  have hi := L2.integrable_inner (𝕜 := ℂ) (thresholdKernelSourceVector e he g hg hs P hP) (oneParticleRadialMap f)
  have hp : (fun q : GW.Space => ⟪thresholdKernelSourceVector e he g hg hs P hP q,oneParticleRadialMap f q⟫_ℂ) =ᵐ[volume]
      (fun q => (fiberFormFactor g (q+P) : ℂ)*(kernelPsi e he g hg hs P q : ℂ)*oneParticleEnergyEmbedding 0 f q) := by
    filter_upwards [thresholdKernelSourceVector_ae e he g hg hs P hP,oneParticleRadialMap_ae f,
      (volume : Measure GW.Space).ae_ne 0] with q hb hu hq
    rw [hb,hu,RCLike.inner_apply']
    exact op02_source_pairing_scalar e he g hg hs P q hq (oneParticleEnergyEmbedding 0 f q)
  refine ⟨hi.congr hp,?_⟩
  rw [L2.inner_def]
  exact integral_congr_ae hp

theorem radial_inner_kernelSource_integral (f : OneParticleEnergySpace 0) :
    Integrable (fun q : GW.Space => (starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f q)*
      (fiberFormFactor g (q+P) : ℂ)*(kernelPsi e he g hg hs P q : ℂ)) volume ∧
    ⟪oneParticleRadialMap f,thresholdKernelSourceVector e he g hg hs P hP⟫_ℂ =
      ∫ q : GW.Space,(starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f q)*
        (fiberFormFactor g (q+P) : ℂ)*(kernelPsi e he g hg hs P q : ℂ) := by
  have hi := L2.integrable_inner (𝕜 := ℂ) (oneParticleRadialMap f) (thresholdKernelSourceVector e he g hg hs P hP)
  have hp : (fun q : GW.Space => ⟪oneParticleRadialMap f q,thresholdKernelSourceVector e he g hg hs P hP q⟫_ℂ) =ᵐ[volume]
      (fun q => (starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f q)*
        (fiberFormFactor g (q+P) : ℂ)*(kernelPsi e he g hg hs P q : ℂ)) := by
    filter_upwards [thresholdKernelSourceVector_ae e he g hg hs P hP,oneParticleRadialMap_ae f,
      (volume : Measure GW.Space).ae_ne 0] with q hb hu hq
    rw [hu,hb,RCLike.inner_apply']
    exact op02_source_pairing_scalar_reverse e he g hg hs P q hq (oneParticleEnergyEmbedding 0 f q)
  refine ⟨hi.congr hp,?_⟩
  rw [L2.inner_def]
  exact integral_congr_ae hp

end Froehlich
