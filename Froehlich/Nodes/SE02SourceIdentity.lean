import Froehlich.Nodes.SE02LeftNormLimit
import Froehlich.Nodes.SE02CutoffLoadIdentification
import Froehlich.Nodes.PT03FormCorrectionSingular

/-! The singular Q1-dual source identity, by uniqueness of actual norm
limits along the explicit cofinal positive natural cutoffs. The right
load has no interpretation as an unweighted singular physical vector. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace Froehlich
variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
  (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2)

theorem se02_source_dual_identity : se02LeftLoad e he g hg hs = se02RightLoad e he g hg hs := by
  have hl : Tendsto (fun n : ℕ => innerSLFlip ℂ
      (se02CutoffLeftEnergy e he g hg hs (GW.Operators.positiveNatCutoff n))) atTop
      (𝓝 (se02LeftLoad e he g hg hs)) :=
    (se02_cutoff_left_load_tendsto e he g hg hs).comp GW.Operators.positiveNatCutoff_tendsto
  have hright : Tendsto
      (fun n : ℕ => se02CutoffWeightedRightLoad e he g hg hs (GW.Operators.positiveNatCutoff n))
      atTop (𝓝 (se02LeftLoad e he g hg hs)) :=
    hl.congr' (Eventually.of_forall (fun n =>
      se02_cutoff_weighted_dual_identity e he g hg hs (GW.Operators.positiveNatCutoff n)))
  exact tendsto_nhds_unique hright (se02_weighted_right_load_tendsto_sequence e he g hg hs)

theorem se02_source_pairing (w : OneParticleEnergySpace 0) :
    Integrable (fun k : GW.Space => ((‖k‖^2-e : ℝ) : ℂ)*
      (starRingEnd ℂ (oneParticleEnergyEmbedding 0 w k))*oneParticleEnergyEmbedding 0 (groundSourceOneEnergy e he g hg hs) k) volume ∧
    Integrable (fun k => (starRingEnd ℂ (oneParticleEnergyEmbedding 0 w k)) *
      (fiberFormFactor g k : ℂ)*(1-(groundSourceLambda e he g hg hs k : ℂ))) volume ∧
    (∫ k : GW.Space, ((‖k‖^2-e : ℝ) : ℂ)*
      (starRingEnd ℂ (oneParticleEnergyEmbedding 0 w k))*oneParticleEnergyEmbedding 0 (groundSourceOneEnergy e he g hg hs) k) -
      ⟪w,singularEnergySchurCorrection e 0 he g hg hs (groundSourceOneEnergy e he g hg hs)⟫_ℂ =
      ∫ k, (starRingEnd ℂ (oneParticleEnergyEmbedding 0 w k)) *
        (fiberFormFactor g k : ℂ)*(1-(groundSourceLambda e he g hg hs k : ℂ)) := by
  have hl := se02_left_load_kinetic_pairing e he g hg hs w
  have hr := se02_right_load_integral e he g hg hs w
  have h := congrArg (fun F : ConjugateLoad (OneParticleEnergySpace 0) => F w)
    (se02_source_dual_identity e he g hg hs)
  exact ⟨hl.1,hr.1,hl.2.symm.trans (h.trans hr.2)⟩

theorem se02_threshold_source_dual_identity (hquarter : |g| ≤ 1/4)
    (heLower : -sectorEnergyConstant * |g|^2 ≤ e)
    (hquadratic : sectorQuadraticConstant * |g|^2 ≤ 1/8) :
    innerSLFlip ℂ ((1-(((1+e : ℝ) : ℂ) • onePhononMassOperator 0)-
      onePhononHighCorrection g e 0 0 hquarter heLower he.2 (by norm_num) hquadratic)
        (groundSourceOneEnergy e he g hg hs)) = se02RightLoad e he g hg hs := by
  have h := se02_source_dual_identity e he g hg hs
  unfold se02LeftLoad se02LeftEnergy at h
  rw [singularEnergySchurCorrection_eq_threshold e 0 he g hg hs hquarter heLower hquadratic] at h
  exact h

theorem se02_threshold_source_pairing (hquarter : |g| ≤ 1/4)
    (heLower : -sectorEnergyConstant * |g|^2 ≤ e)
    (hquadratic : sectorQuadraticConstant * |g|^2 ≤ 1/8) (w : OneParticleEnergySpace 0) :
    Integrable (fun k : GW.Space => ((‖k‖^2-e : ℝ) : ℂ)*
      (starRingEnd ℂ (oneParticleEnergyEmbedding 0 w k))*oneParticleEnergyEmbedding 0 (groundSourceOneEnergy e he g hg hs) k) volume ∧
    Integrable (fun k => (starRingEnd ℂ (oneParticleEnergyEmbedding 0 w k)) *
      (fiberFormFactor g k : ℂ)*(1-(groundSourceLambda e he g hg hs k : ℂ))) volume ∧
    (∫ k : GW.Space, ((‖k‖^2-e : ℝ) : ℂ)*
      (starRingEnd ℂ (oneParticleEnergyEmbedding 0 w k))*oneParticleEnergyEmbedding 0 (groundSourceOneEnergy e he g hg hs) k) -
      ⟪w,onePhononHighCorrection g e 0 0 hquarter heLower he.2 (by norm_num) hquadratic
        (groundSourceOneEnergy e he g hg hs)⟫_ℂ =
      ∫ k, (starRingEnd ℂ (oneParticleEnergyEmbedding 0 w k)) *
        (fiberFormFactor g k : ℂ)*(1-(groundSourceLambda e he g hg hs k : ℂ)) := by
  have h := se02_source_pairing e he g hg hs w
  rw [singularEnergySchurCorrection_eq_threshold e 0 he g hg hs hquarter heLower hquadratic] at h
  exact h

end Froehlich
