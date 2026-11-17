import Froehlich.Nodes.PT03FormCorrectionKinetic
import Froehlich.Nodes.PT03BoundsDiagonalContinuity

set_option autoImplicit false

/-! The actual full scalar diagonal is absolutely integrable on the
weighted one-particle domain, with its exact kinetic/self-energy signs. -/
noncomputable section
open MeasureTheory
namespace Froehlich

 theorem thresholdFullDiagonal_integrable_and_combine (e : ℝ)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P : GW.Space) (f h : OneParticleEnergySpace P) :
    Integrable (fun k : GW.Space => (starRingEnd ℂ) (oneParticleEnergyEmbedding P f k)*
      ((‖k-P‖^2+auxiliarySelfEnergy e (k-P) he g hg hs-e : ℝ) : ℂ)*oneParticleEnergyEmbedding P h k) volume ∧
    (∫ k : GW.Space, ((‖k-P‖^2-e : ℝ) : ℂ)*(starRingEnd ℂ) (oneParticleEnergyEmbedding P f k)*
      oneParticleEnergyEmbedding P h k) -
    (∫ k : GW.Space, (starRingEnd ℂ) (oneParticleEnergyEmbedding P f k)*
      (-(auxiliarySelfEnergy e (k-P) he g hg hs : ℂ))*oneParticleEnergyEmbedding P h k) =
    ∫ k : GW.Space, (starRingEnd ℂ) (oneParticleEnergyEmbedding P f k)*
      ((‖k-P‖^2+auxiliarySelfEnergy e (k-P) he g hg hs-e : ℝ) : ℂ)*oneParticleEnergyEmbedding P h k := by
  have hfree := (oneParticle_threshold_free_integral e P f h).1
  have hdiag := singularThresholdDiagonal_shift_integrable e he g hg hs P
    (oneParticleEnergyEmbedding P f) (oneParticleEnergyEmbedding P h)
  have hpoint : (fun k : GW.Space =>
      ((‖k-P‖^2-e : ℝ) : ℂ)*(starRingEnd ℂ) (oneParticleEnergyEmbedding P f k)*oneParticleEnergyEmbedding P h k -
      (starRingEnd ℂ) (oneParticleEnergyEmbedding P f k)*(-(auxiliarySelfEnergy e (k-P) he g hg hs : ℂ))*
        oneParticleEnergyEmbedding P h k) =ᵐ[volume]
      (fun k => (starRingEnd ℂ) (oneParticleEnergyEmbedding P f k)*
        ((‖k-P‖^2+auxiliarySelfEnergy e (k-P) he g hg hs-e : ℝ) : ℂ)*oneParticleEnergyEmbedding P h k) :=
    Filter.Eventually.of_forall (fun k => by push_cast; ring)
  refine ⟨(hfree.sub hdiag).congr hpoint,?_⟩
  exact (integral_sub hfree hdiag).symm.trans (integral_congr_ae hpoint)

theorem translatedThresholdFullDiagonal_integrable (e : ℝ)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (f h : OneParticleEnergySpace 0) :
    Integrable (fun q : GW.Space => (starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f q)*
      ((‖q‖^2+auxiliarySelfEnergy e q he g hg hs-e : ℝ) : ℂ)*oneParticleEnergyEmbedding 0 h q) volume := by
  simpa only [sub_zero] using (thresholdFullDiagonal_integrable_and_combine e he g hg hs 0 f h).1

end Froehlich
