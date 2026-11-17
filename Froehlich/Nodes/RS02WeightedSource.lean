import Froehlich.Nodes.RS02SourceEnergy
import Froehlich.Nodes.RS02SourceJetsIdentification

set_option autoImplicit false

/-! The literal high-sector membership and W-graph bound of the actual h. -/
noncomputable section
namespace Froehlich

theorem auxiliaryGroundSourceVector_mem_high (g e : ℝ) (p : GW.Space)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) :
    auxiliaryGroundSourceVector e p he g hg hs ∈ HighSectorSpace 1 := by
  change (highEnergyEmbedding (-p) 1 (auxiliaryGroundSourceEnergy e p he g hg hs) : GW.Fock.Carrier) ∈ _
  exact (highEnergyEmbedding (-p) 1 (auxiliaryGroundSourceEnergy e p he g hg hs)).property

theorem auxiliaryGroundSourceWeighted_uniform_linear : ∃ C : ℝ, 0 < C ∧
    ∀ (g e : ℝ) (p : GW.Space) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
      (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2),
      ‖auxiliaryGroundSourceWeighted g e p he hg hs‖ ≤ C*|g| := by
  obtain ⟨Cz,hCz,hz⟩ := auxiliarySourceJets_uniform_bound
  refine ⟨2*Cz,by positivity,?_⟩
  intro g e p he hg hs
  have hZ : ‖auxiliaryNormalizedSource g e p he.2‖ ≤ Cz*|g| := by
    rw [auxiliaryNormalizedSource_eq_sourceJetHigh g e p he,auxiliarySourceJetHigh_norm]
    simpa only [List.length_nil,scalarDerivativeCoefficientBound,one_mul] using! hz [] g e p he.2
  calc
    _ ≤ 2*‖auxiliaryNormalizedSource g e p he.2‖ := auxiliaryGroundSourceWeighted_norm_le g e p he hg hs
    _ ≤ 2*(Cz*|g|) := mul_le_mul_of_nonneg_left hZ (by norm_num)
    _ = _ := by ring

end Froehlich
