import Froehlich.Nodes.SE02SourceIdentity
import Froehlich.Nodes.PT03FormCorrectionGround

/-! SE02 / lem:keyidentity, as an equality in the complete Q1 conjugate
dual. The actual SP03 correction and literal weighted singular load are
constructed internally. No unweighted singular right vector or c₀ division. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace Froehlich

def SE02FixedReference (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2)
    (hquarter : |g| ≤ 1/4) (heLower : -sectorEnergyConstant * |g|^2 ≤ e)
    (hquadratic : sectorQuadraticConstant * |g|^2 ≤ 1/8) : Prop :=
  se02LeftLoad e he g hg hs = se02RightLoad e he g hg hs ∧
  innerSLFlip ℂ ((1-(((1+e : ℝ) : ℂ) • onePhononMassOperator 0)-
    onePhononHighCorrection g e 0 0 hquarter heLower he.2 (by norm_num) hquadratic)
      (groundSourceOneEnergy e he g hg hs)) = se02RightLoad e he g hg hs ∧
  ∀ w : OneParticleEnergySpace 0,
    Integrable (fun k : GW.Space => ((‖k‖^2-e : ℝ) : ℂ)*
      (starRingEnd ℂ (oneParticleEnergyEmbedding 0 w k))*oneParticleEnergyEmbedding 0 (groundSourceOneEnergy e he g hg hs) k) volume ∧
    Integrable (fun k => (starRingEnd ℂ (oneParticleEnergyEmbedding 0 w k)) *
      (fiberFormFactor g k : ℂ)*(1-(groundSourceLambda e he g hg hs k : ℂ))) volume ∧
    (∫ k : GW.Space, ((‖k‖^2-e : ℝ) : ℂ)*
      (starRingEnd ℂ (oneParticleEnergyEmbedding 0 w k))*oneParticleEnergyEmbedding 0 (groundSourceOneEnergy e he g hg hs) k) -
      ⟪w,onePhononHighCorrection g e 0 0 hquarter heLower he.2 (by norm_num) hquadratic
        (groundSourceOneEnergy e he g hg hs)⟫_ℂ =
      ∫ k, (starRingEnd ℂ (oneParticleEnergyEmbedding 0 w k)) *
        (fiberFormFactor g k : ℂ)*(1-(groundSourceLambda e he g hg hs k : ℂ))

/-- Exact convergence scopes used in the proof: the left side converges
on the full cutoff filter, while the weighted-right DCT is invoked along
the explicit cofinal natural cutoffs, sufficient for uniqueness of limits. -/
def SE02NormPassage (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2) : Prop :=
  Tendsto (cutoffGroundSourceOneEnergy e he g hg hs) atTop (𝓝 (groundSourceOneEnergy e he g hg hs)) ∧
  Tendsto (fun Λ : GW.Operators.PositiveCutoff => innerSLFlip ℂ (se02CutoffLeftEnergy e he g hg hs Λ))
    atTop (𝓝 (se02LeftLoad e he g hg hs)) ∧
  Tendsto (fun n : ℕ => se02CutoffWeightedRightLoad e he g hg hs (GW.Operators.positiveNatCutoff n))
    atTop (𝓝 (se02RightLoad e he g hg hs)) ∧
  ∀ Λ : GW.Operators.PositiveCutoff,
    innerSLFlip ℂ (se02CutoffLeftEnergy e he g hg hs Λ) = se02CutoffWeightedRightLoad e he g hg hs Λ

theorem finalSE02_uniform (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2)
    (hquarter : |g| ≤ 1/4) (heLower : -sectorEnergyConstant * |g|^2 ≤ e)
    (hquadratic : sectorQuadraticConstant * |g|^2 ≤ 1/8) :
    SE02FixedReference e he g hg hs hquarter heLower hquadratic ∧ SE02NormPassage e he g hg hs := by
  constructor
  · exact ⟨se02_source_dual_identity e he g hg hs,
      se02_threshold_source_dual_identity e he g hg hs hquarter heLower hquadratic,
      se02_threshold_source_pairing e he g hg hs hquarter heLower hquadratic⟩
  · exact ⟨se02_cutoff_one_energy_tendsto e he g hg hs,se02_cutoff_left_load_tendsto e he g hg hs,
      se02_weighted_right_load_tendsto_sequence e he g hg hs,se02_cutoff_weighted_dual_identity e he g hg hs⟩

theorem finalSE02 : ∃ s : ℝ, 0 < s ∧ ∀ g : ℝ, |g| < s →
    ∃ he : groundEnergy (fiberHamiltonian g 0) ∈ Set.Icc (-1/4 : ℝ) 0,
    ∃ hg : |g| ≤ 1, ∃ hs : auxiliaryResolventConstant * |g| ≤ 1/2,
    ∃ hquarter : |g| ≤ 1/4,
    ∃ heLower : -sectorEnergyConstant * |g|^2 ≤ groundEnergy (fiberHamiltonian g 0),
    ∃ hquadratic : sectorQuadraticConstant * |g|^2 ≤ 1/8,
      SE02FixedReference (groundEnergy (fiberHamiltonian g 0)) he g hg hs hquarter heLower hquadratic ∧
      SE02NormPassage (groundEnergy (fiberHamiltonian g 0)) he g hg hs := by
  obtain ⟨s,hs,hSmall⟩ := pt03_ground_reference_smallness
  refine ⟨s,hs,?_⟩
  intro g hgSmall
  obtain ⟨he,hg,haux,hquarter,heLower,hquadratic⟩ := hSmall g hgSmall
  exact ⟨he,hg,haux,hquarter,heLower,hquadratic,
    finalSE02_uniform _ he g hg haux hquarter heLower hquadratic⟩

end Froehlich
