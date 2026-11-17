import Froehlich.Nodes.PT03KernelDefinitions
import Froehlich.Nodes.TR01

set_option autoImplicit false

/-! The exact single-integral translation of the kinetic/self-energy term.
This is a measure change of variables, separate from form identification. -/
noncomputable section
open MeasureTheory
namespace Froehlich

theorem pt03_energyInverseTranslation_physical_ae (P : GW.Space) (f : OneParticleEnergySpace 0) :
    (fun q => oneParticleEnergyEmbedding P ((energyTranslation P).symm f) (q+P)) =ᵐ[volume]
      (fun q => oneParticleEnergyEmbedding 0 f q) := by
  have h := momentumTranslation_ae P (oneParticleEnergyEmbedding P ((energyTranslation P).symm f))
  rw [←energyTranslation_intertwines,LinearIsometryEquiv.apply_symm_apply] at h
  filter_upwards [h] with q hq
  exact hq.symm

theorem thresholdScalar_translation_integral (e : ℝ)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P : GW.Space) (f h : OneParticleEnergySpace 0) :
    (∫ k : GW.Space,
      (starRingEnd ℂ) (oneParticleEnergyEmbedding P ((energyTranslation P).symm f) k)*
        ((‖k-P‖^2+auxiliarySelfEnergy e (k-P) he g hg hs-e : ℝ) : ℂ)*
          oneParticleEnergyEmbedding P ((energyTranslation P).symm h) k) =
    ∫ q : GW.Space, (starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f q)*
      ((‖q‖^2+auxiliarySelfEnergy e q he g hg hs-e : ℝ) : ℂ)*oneParticleEnergyEmbedding 0 h q := by
  let G := fun k : GW.Space =>
    (starRingEnd ℂ) (oneParticleEnergyEmbedding P ((energyTranslation P).symm f) k)*
      ((‖k-P‖^2+auxiliarySelfEnergy e (k-P) he g hg hs-e : ℝ) : ℂ)*
        oneParticleEnergyEmbedding P ((energyTranslation P).symm h) k
  calc
    _ = ∫ q : GW.Space, G (q+P) := (integral_add_right_eq_self G P).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [pt03_energyInverseTranslation_physical_ae P f,
        pt03_energyInverseTranslation_physical_ae P h] with q hf hh
      simp only [G,add_sub_cancel_right]
      rw [hf,hh]

end Froehlich
