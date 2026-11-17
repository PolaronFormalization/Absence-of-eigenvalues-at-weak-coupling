import Froehlich.Nodes.KA01NumberPairing

/-! The V_N formulation uses the actual retained square-root-number domain.
Its coordinate lift is defined only on that domain, with exact physical embedding. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

def numberDomainLift (u : (GW.Fock.numberPower GW.Fock.Sector (1/2)).domain) : NumberFormSpace :=
  Classical.choose (numberFormEmbedding_range.symm.subset u.property)

theorem numberDomainLift_embedding
    (u : (GW.Fock.numberPower GW.Fock.Sector (1/2)).domain) :
    numberFormEmbedding (numberDomainLift u) = (u : GW.Fock.Carrier) :=
  Classical.choose_spec (numberFormEmbedding_range.symm.subset u.property)

theorem numberDomainLift_unique
    (u : (GW.Fock.numberPower GW.Fock.Sector (1/2)).domain)
    (x : NumberFormSpace) (hx : numberFormEmbedding x = (u : GW.Fock.Carrier)) :
    x = numberDomainLift u :=
  numberFormEmbedding_injective (hx.trans (numberDomainLift_embedding u).symm)

theorem oneToHighAdjoint_numberDomain_ae (v : GW.OnePhonon) (z : HighSectorSpace 2)
    (hz : (z : GW.Fock.Carrier) ∈ (GW.Fock.numberPower GW.Fock.Sector (1/2)).domain) :
    ∀ᵐ k ∂(volume : Measure GW.Space), oneToHighAdjoint v z k =
      ⟪oneParticleInclusion v,annihilationField (numberDomainLift ⟨(z : GW.Fock.Carrier),hz⟩) k⟫_ℂ :=
  oneToHighAdjoint_numberField_ae v (numberDomainLift ⟨(z : GW.Fock.Carrier),hz⟩) z
    (numberDomainLift_embedding ⟨(z : GW.Fock.Carrier),hz⟩)

end Froehlich
