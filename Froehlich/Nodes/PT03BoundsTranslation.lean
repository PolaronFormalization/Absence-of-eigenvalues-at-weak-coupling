import Froehlich.Nodes.PT03BoundsTranslatedIntegrability
import Froehlich.Nodes.PT03FormKernelIntegrability

set_option autoImplicit false

/-! Exact product change of variables for the actual C kernel, using the
retained physical energy translation and genuine volume translation. -/
noncomputable section
open MeasureTheory
namespace Froehlich

private theorem pt03_translated_embedding_ae (P : GW.Space) (f : OneParticleEnergySpace 0) :
    (fun q => oneParticleEnergyEmbedding P ((energyTranslation P).symm f) (q+P)) =ᵐ[volume]
      (fun q => oneParticleEnergyEmbedding 0 f q) := by
  rw [energyTranslation_symm_intertwines,momentumTranslation_symm_apply]
  have h := (space_translation_preserving P).quasiMeasurePreserving.ae
    (GW.Analysis.translation_ae P (oneParticleEnergyEmbedding 0 f))
  filter_upwards [h] with q hq
  simpa only [add_sub_cancel_right] using hq

theorem thresholdKernelC_translation_integral (e : ℝ)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P : GW.Space) (_hP : ‖P‖ ≤ 1/4)
    (f h : OneParticleEnergySpace 0) :
    (∫ x : GW.Space × GW.Space,
      (starRingEnd ℂ) (oneParticleEnergyEmbedding P ((energyTranslation P).symm f) x.1)*
        (fiberFormFactor g x.1 : ℂ)*thresholdKernelC e he g hg hs P (x.1-P) (x.2-P)*
          (fiberFormFactor g x.2 : ℂ)*oneParticleEnergyEmbedding P ((energyTranslation P).symm h) x.2
      ∂(volume.prod volume)) =
    ∫ x : GW.Space × GW.Space,
      (starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f x.1)*(fiberFormFactor g (x.1+P) : ℂ)*
        thresholdKernelC e he g hg hs P x.1 x.2*(fiberFormFactor g (x.2+P) : ℂ)*
          oneParticleEnergyEmbedding 0 h x.2 ∂(volume.prod volume) := by
  let G := fun x : GW.Space × GW.Space =>
    (starRingEnd ℂ) (oneParticleEnergyEmbedding P ((energyTranslation P).symm f) x.1)*
      (fiberFormFactor g x.1 : ℂ)*thresholdKernelC e he g hg hs P (x.1-P) (x.2-P)*
        (fiberFormFactor g x.2 : ℂ)*oneParticleEnergyEmbedding P ((energyTranslation P).symm h) x.2
  let T := Prod.map (fun q : GW.Space => q+P) (fun r : GW.Space => r+P)
  have hm : MeasurePreserving T (volume.prod volume) (volume.prod volume) :=
    (space_translation_preserving P).prod (space_translation_preserving P)
  have hemb : MeasurableEmbedding T :=
    (MeasurableEquiv.addRight P).measurableEmbedding.prodMap (MeasurableEquiv.addRight P).measurableEmbedding
  have hF := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure GW.Space))
    (ν := (volume : Measure GW.Space))).ae (pt03_translated_embedding_ae P f)
  have hH := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure GW.Space))
    (ν := (volume : Measure GW.Space))).ae (pt03_translated_embedding_ae P h)
  calc
    _ = ∫ x : GW.Space × GW.Space, G (T x) ∂(volume.prod volume) :=
      (hm.integral_comp hemb G).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hF,hH] with x hf hh
      simp only [G,T,Prod.map,add_sub_cancel_right]
      rw [hf,hh]

end Froehlich
