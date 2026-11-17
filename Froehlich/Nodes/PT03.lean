import Froehlich.Nodes.PT03FormTranslated
import Froehlich.Nodes.PT03FormCorrectionGround

set_option autoImplicit false

/-! PT03 / lem:kernelformula: the actual translated threshold form,
including absolute convergence, at the literal uncut ground reference. -/
noncomputable section
open MeasureTheory
namespace Froehlich

def PT03FixedReference (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (hquarter : |g| ≤ 1/4) (heLower : -sectorEnergyConstant*|g|^2 ≤ e)
    (hquadratic : sectorQuadraticConstant*|g|^2 ≤ 1/8) : Prop :=
  ∀ (P : GW.Space) (hP : ‖P‖ ≤ 1/4) (f h : OneParticleEnergySpace 0),
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
            oneParticleEnergyEmbedding 0 h x.2 ∂volume.prod volume

theorem finalPT03_uniform (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (hquarter : |g| ≤ 1/4) (heLower : -sectorEnergyConstant*|g|^2 ≤ e)
    (hquadratic : sectorQuadraticConstant*|g|^2 ≤ 1/8) :
    PT03FixedReference e he g hg hs hquarter heLower hquadratic := by
  intro P hP f h
  exact translatedThresholdForm_kernel_formula e he g hg hs hquarter heLower hquadratic P hP f h

theorem finalPT03 : ∃ s : ℝ, 0 < s ∧ ∀ g : ℝ, |g| < s →
    ∃ he : groundEnergy (fiberHamiltonian g 0) ∈ Set.Icc (-1/4 : ℝ) 0,
    ∃ hg : |g| ≤ 1, ∃ hs : auxiliaryResolventConstant*|g| ≤ 1/2,
    ∃ hquarter : |g| ≤ 1/4,
    ∃ heLower : -sectorEnergyConstant*|g|^2 ≤ groundEnergy (fiberHamiltonian g 0),
    ∃ hquadratic : sectorQuadraticConstant*|g|^2 ≤ 1/8,
      PT03FixedReference (groundEnergy (fiberHamiltonian g 0)) he g hg hs hquarter heLower hquadratic := by
  obtain ⟨s,hs,hSmall⟩ := pt03_ground_reference_smallness
  refine ⟨s,hs,?_⟩
  intro g hgSmall
  obtain ⟨he,hg,haux,hquarter,heLower,hquadratic⟩ := hSmall g hgSmall
  exact ⟨he,hg,haux,hquarter,heLower,hquadratic,
    finalPT03_uniform _ he g hg haux hquarter heLower hquadratic⟩

end Froehlich
