import Froehlich.Nodes.SE02CutoffDual
import Froehlich.Nodes.SE02WeightedRightSource

/-! The cutoff-only Hilbert-space calculation and the weighted-dual
construction define the SAME load. The singular source is presented only
by its absolutely convergent pairing with full Q1 tests. -/
noncomputable section
open MeasureTheory
namespace Froehlich
variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
  (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2)

theorem se02_right_load_integral (w : OneParticleEnergySpace 0) :
    Integrable (fun k => (starRingEnd ℂ (oneParticleEnergyEmbedding 0 w k)) *
      (fiberFormFactor g k : ℂ)*(1-(groundSourceLambda e he g hg hs k : ℂ))) volume ∧
    se02RightLoad e he g hg hs w =
      ∫ k, (starRingEnd ℂ (oneParticleEnergyEmbedding 0 w k)) *
        (fiberFormFactor g k : ℂ)*(1-(groundSourceLambda e he g hg hs k : ℂ)) := by
  have hi := weightedSource_pairing_integrable (oneParticleEnergyWeight 0)
    (oneParticleEnergyWeight_measurable 0) (oneParticleEnergyWeight_ge_one 0)
    (se02RightCoefficient e he g hg hs) (se02_right_quotient_memLp e he g hg hs) w
  have hp : (fun k => (starRingEnd ℂ (oneParticleEnergyEmbedding 0 w k))*se02RightCoefficient e he g hg hs k)
      =ᵐ[volume] (fun k => (starRingEnd ℂ (oneParticleEnergyEmbedding 0 w k)) *
        (fiberFormFactor g k : ℂ)*(1-(groundSourceLambda e he g hg hs k : ℂ))) :=
    Filter.Eventually.of_forall (fun k => by unfold se02RightCoefficient; ring)
  have heq := weightedSourceLoad_integral (oneParticleEnergyWeight 0)
    (oneParticleEnergyWeight_measurable 0) (oneParticleEnergyWeight_ge_one 0)
    (se02RightCoefficient e he g hg hs) (se02_right_quotient_memLp e he g hg hs) w
  exact ⟨hi.congr hp,heq.trans (integral_congr_ae hp)⟩

theorem se02_cutoff_weighted_right_load_integral (Λ : GW.Operators.PositiveCutoff) (w : OneParticleEnergySpace 0) :
    Integrable (fun k => (starRingEnd ℂ (oneParticleEnergyEmbedding 0 w k)) *
      (cutoffFormFactor g Λ.val k : ℂ)*(1-cutoffThresholdKernelJ e he g hg hs Λ 0 k 0)) volume ∧
    se02CutoffWeightedRightLoad e he g hg hs Λ w =
      ∫ k, (starRingEnd ℂ (oneParticleEnergyEmbedding 0 w k)) *
        (cutoffFormFactor g Λ.val k : ℂ)*(1-cutoffThresholdKernelJ e he g hg hs Λ 0 k 0) := by
  have hi := weightedSource_pairing_integrable (oneParticleEnergyWeight 0)
    (oneParticleEnergyWeight_measurable 0) (oneParticleEnergyWeight_ge_one 0)
    (se02CutoffRightCoefficient e he g hg hs Λ) (se02_cutoff_right_quotient_memLp e he g hg hs Λ) w
  have hp : (fun k => (starRingEnd ℂ (oneParticleEnergyEmbedding 0 w k))*se02CutoffRightCoefficient e he g hg hs Λ k)
      =ᵐ[volume] (fun k => (starRingEnd ℂ (oneParticleEnergyEmbedding 0 w k)) *
        (cutoffFormFactor g Λ.val k : ℂ)*(1-cutoffThresholdKernelJ e he g hg hs Λ 0 k 0)) :=
    Filter.Eventually.of_forall (fun k => by unfold se02CutoffRightCoefficient; ring)
  have heq := weightedSourceLoad_integral (oneParticleEnergyWeight 0)
    (oneParticleEnergyWeight_measurable 0) (oneParticleEnergyWeight_ge_one 0)
    (se02CutoffRightCoefficient e he g hg hs Λ) (se02_cutoff_right_quotient_memLp e he g hg hs Λ) w
  exact ⟨hi.congr hp,heq.trans (integral_congr_ae hp)⟩

theorem se02_cutoff_right_load_eq_weighted (Λ : GW.Operators.PositiveCutoff) :
    se02CutoffRightLoad e he g hg hs Λ = se02CutoffWeightedRightLoad e he g hg hs Λ := by
  apply ContinuousLinearMap.ext
  intro w
  exact (se02_cutoff_rhs_integral e he g hg hs Λ w).2.trans
    (se02_cutoff_weighted_right_load_integral e he g hg hs Λ w).2.symm

theorem se02_cutoff_weighted_dual_identity (Λ : GW.Operators.PositiveCutoff) :
    innerSLFlip ℂ (se02CutoffLeftEnergy e he g hg hs Λ) = se02CutoffWeightedRightLoad e he g hg hs Λ :=
  (se02_cutoff_dual_identity e he g hg hs Λ).trans (se02_cutoff_right_load_eq_weighted e he g hg hs Λ)

end Froehlich
