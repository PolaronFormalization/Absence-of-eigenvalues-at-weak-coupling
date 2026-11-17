import Froehlich.Nodes.FB01Forms
import Froehlich.Nodes.FC01Lifts

noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem coreEnergyNumberCoordinates_eq (P : GW.Space) (u : boundedMomentumCore) :
    energyNumberCoordinates P (coreEnergyLift P u) = coreNumberLift u := by
  apply numberFormEmbedding_injective
  rw [energyNumberCoordinates_intertwines, coreEnergyLift_embedding, coreNumberLift_embedding]

theorem boundedEnergyInteraction_core_apply (P : GW.Space) (f : GW.OnePhonon)
    (w u : boundedMomentumCore) :
    boundedEnergyInteraction P f (coreEnergyLift P w) (coreEnergyLift P u) =
      ⟪(w : GW.Fock.Carrier),fieldRestriction f (coreNumberLift u)⟫_ℂ := by
  rw [boundedEnergyInteraction_apply, energyInteractionForm_apply]
  change ⟪energyEmbedding P (coreEnergyLift P w),
    fieldRestriction f (energyNumberCoordinates P (coreEnergyLift P u))⟫_ℂ = _
  rw [coreEnergyLift_embedding, coreEnergyNumberCoordinates_eq]

theorem boundedEnergyInteraction_core_momentum_independent (P Q : GW.Space) (f : GW.OnePhonon)
    (w u : boundedMomentumCore) :
    boundedEnergyInteraction P f (coreEnergyLift P w) (coreEnergyLift P u) =
      boundedEnergyInteraction Q f (coreEnergyLift Q w) (coreEnergyLift Q u) := by
  rw [boundedEnergyInteraction_core_apply, boundedEnergyInteraction_core_apply]

theorem cutoffInteractionForm_core_apply (g Λ : ℝ) (hΛ : 0 < Λ) (P : GW.Space)
    (w u : boundedMomentumCore) :
    cutoffInteractionForm g Λ hΛ P (coreEnergyLift P w) (coreEnergyLift P u) =
      ⟪(w : GW.Fock.Carrier),GW.Fock.ordinaryField (cutoffFormFactorL2 g Λ hΛ)
        (numberFormRootInput (coreNumberLift u))⟫_ℂ := by
  change boundedEnergyInteraction P (cutoffFormFactorL2 g Λ hΛ)
    (coreEnergyLift P w) (coreEnergyLift P u) = _
  rw [boundedEnergyInteraction_core_apply, fieldRestriction_eq_ordinaryField]

end Froehlich
