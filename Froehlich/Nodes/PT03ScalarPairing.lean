import Froehlich.Nodes.PT03ScalarCreation
import Froehlich.Nodes.PT01CoreTesting

set_option autoImplicit false

/-! The one-to-high pairing is an ordinary absolutely integrable scalar
field pairing, only for inputs in the genuine number domain. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

theorem oneToHighMap_pairing_integral (v f : GW.OnePhonon) (z : NumberFormSpace) :
    Integrable (fun k => (starRingEnd ℂ) (f k)*⟪oneParticleInclusion v,annihilationField z k⟫_ℂ) volume ∧
    ⟪(oneToHighMap v f : GW.Fock.Carrier),numberFormEmbedding z⟫_ℂ =
      ∫ k, (starRingEnd ℂ) (f k)*⟪oneParticleInclusion v,annihilationField z k⟫_ℂ := by
  have h := smearedCreation_test_integral f (numberOneParticleLift v) z
  have hc : creationRestriction f (numberOneParticleLift v) = (oneToHighMap v f : GW.Fock.Carrier) := by
    rw [←oneToHighMap_eq_creation,oneToHighMap_exchange]
  constructor
  · simpa only [numberFormEmbedding_oneParticleLift] using h.1
  · have he := h.2
    rw [numberFormEmbedding_oneParticleLift,hc] at he
    exact he.symm

end Froehlich
