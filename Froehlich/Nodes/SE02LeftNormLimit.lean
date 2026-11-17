import Froehlich.Nodes.SE02CutoffDual
import Froehlich.Nodes.PT02SourceConvergence
import Froehlich.Nodes.UV01CorrectionError
import Froehlich.Nodes.PT03FormCorrectionKinetic

/-! Actual cutoff f₀ convergence in Q1, followed by convergence of the
kinetic-minus-correction load in the complete conjugate-dual norm.
All cutoff parameters use the same e. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace Froehlich

private theorem se02_apply_tendsto {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : GW.Operators.PositiveCutoff → E →L[ℂ] E) (S : E →L[ℂ] E)
    (v : GW.Operators.PositiveCutoff → E) (w : E)
    (hT : Tendsto T atTop (𝓝 S)) (hv : Tendsto v atTop (𝓝 w)) :
    Tendsto (fun Λ => T Λ (v Λ)) atTop (𝓝 (S w)) :=
  (((ContinuousLinearMap.id ℂ (E →L[ℂ] E)).continuous₂).tendsto (S,w)).comp (hT.prodMk_nhds hv)

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
  (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2)

theorem se02_cutoff_one_energy_tendsto :
    Tendsto (cutoffGroundSourceOneEnergy e he g hg hs) atTop (𝓝 (groundSourceOneEnergy e he g hg hs)) := by
  let B : HighEnergySpace (-(0 : GW.Space)) 1 →L[ℂ] OneParticleEnergySpace 0 :=
    (oneParticleEnergyProjection 0).comp
      ((HighEnergySpace 0 1).subtypeL.comp (highEnergyCoordinateChange 0 (-(0 : GW.Space)) 1))
  exact (B.continuous.tendsto (auxiliaryGroundSourceEnergy e 0 he g hg hs)).comp
    (cutoffGroundSourceEnergy_tendsto e 0 he g hg hs)

def se02LeftEnergy : OneParticleEnergySpace 0 :=
  (1-(((1+e : ℝ) : ℂ) • onePhononMassOperator 0)-singularEnergySchurCorrection e 0 he g hg hs)
    (groundSourceOneEnergy e he g hg hs)

def se02LeftLoad : ConjugateLoad (OneParticleEnergySpace 0) := innerSLFlip ℂ (se02LeftEnergy e he g hg hs)

theorem se02_cutoff_left_energy_tendsto :
    Tendsto (se02CutoffLeftEnergy e he g hg hs) atTop (𝓝 (se02LeftEnergy e he g hg hs)) := by
  have hf := se02_cutoff_one_energy_tendsto e he g hg hs
  let K : OneParticleEnergySpace 0 →L[ℂ] OneParticleEnergySpace 0 :=
    1-(((1+e : ℝ) : ℂ) • onePhononMassOperator 0)
  have hfree := (K.continuous.tendsto (groundSourceOneEnergy e he g hg hs)).comp hf
  have hD := se02_apply_tendsto (cutoffEnergySchurCorrection e 0 he g hg hs)
    (singularEnergySchurCorrection e 0 he g hg hs)
    (cutoffGroundSourceOneEnergy e he g hg hs) (groundSourceOneEnergy e he g hg hs)
    (cutoffEnergySchurCorrection_tendsto e 0 he g hg hs) hf
  have hlim := hfree.sub hD
  simp only [Function.comp_def,Pi.sub_def] at hlim
  have hfun : (fun Λ : GW.Operators.PositiveCutoff => K (cutoffGroundSourceOneEnergy e he g hg hs Λ) -
      cutoffEnergySchurCorrection e 0 he g hg hs Λ (cutoffGroundSourceOneEnergy e he g hg hs Λ)) =
      se02CutoffLeftEnergy e he g hg hs := by
    funext Λ
    rfl
  have htarget : K (groundSourceOneEnergy e he g hg hs) -
      singularEnergySchurCorrection e 0 he g hg hs (groundSourceOneEnergy e he g hg hs) =
      se02LeftEnergy e he g hg hs := rfl
  rw [hfun,htarget] at hlim
  exact hlim

theorem se02_cutoff_left_load_tendsto :
    Tendsto (fun Λ : GW.Operators.PositiveCutoff => innerSLFlip ℂ (se02CutoffLeftEnergy e he g hg hs Λ))
      atTop (𝓝 (se02LeftLoad e he g hg hs)) := by
  let R : OneParticleEnergySpace 0 →L[ℂ] ConjugateLoad (OneParticleEnergySpace 0) := innerSLFlip ℂ
  exact (R.continuous.tendsto (se02LeftEnergy e he g hg hs)).comp
    (se02_cutoff_left_energy_tendsto e he g hg hs)

theorem se02_left_load_kinetic_pairing (w : OneParticleEnergySpace 0) :
    Integrable (fun k : GW.Space => ((‖k‖^2-e : ℝ) : ℂ)*
      (starRingEnd ℂ (oneParticleEnergyEmbedding 0 w k))*oneParticleEnergyEmbedding 0 (groundSourceOneEnergy e he g hg hs) k) volume ∧
    se02LeftLoad e he g hg hs w =
      (∫ k : GW.Space, ((‖k‖^2-e : ℝ) : ℂ)*
        (starRingEnd ℂ (oneParticleEnergyEmbedding 0 w k))*oneParticleEnergyEmbedding 0 (groundSourceOneEnergy e he g hg hs) k) -
      ⟪w,singularEnergySchurCorrection e 0 he g hg hs (groundSourceOneEnergy e he g hg hs)⟫_ℂ := by
  have h := oneParticle_threshold_free_integral e 0 w (groundSourceOneEnergy e he g hg hs)
  simp only [sub_zero] at h
  refine ⟨h.1,?_⟩
  change ⟪w,se02LeftEnergy e he g hg hs⟫_ℂ = _
  simp only [se02LeftEnergy,sub_apply,one_apply_eq_self,smul_apply,inner_sub_right,
    inner_smul_right,pt03_onePhononMassOperator_pairing]
  rw [h.2]

end Froehlich
