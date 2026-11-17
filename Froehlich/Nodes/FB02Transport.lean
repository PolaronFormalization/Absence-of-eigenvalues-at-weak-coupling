import Froehlich.Nodes.FB01Forms

/-! Cutoff interactions are one physical form on the common energy domain. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem energyNumberCoordinates_change (P Q : GW.Space) (u : EnergySpace Q) :
    energyNumberCoordinates P (energyCoordinateChange P Q u) = energyNumberCoordinates Q u := by
  apply numberFormEmbedding_injective
  rw [energyNumberCoordinates_intertwines, energyNumberCoordinates_intertwines,
    energyCoordinateChange_intertwines]

theorem boundedEnergyInteraction_change (P Q : GW.Space) (f : GW.OnePhonon)
    (w u : EnergySpace Q) :
    boundedEnergyInteraction P f (energyCoordinateChange P Q w) (energyCoordinateChange P Q u) =
      boundedEnergyInteraction Q f w u := by
  change energyInteractionForm P f (energyCoordinateChange P Q w) (energyCoordinateChange P Q u) =
    energyInteractionForm Q f w u
  rw [energyInteractionForm_apply, energyInteractionForm_apply]
  change ⟪energyEmbedding P (energyCoordinateChange P Q w),
    fieldRestriction f (energyNumberCoordinates P (energyCoordinateChange P Q u))⟫_ℂ = _
  rw [energyCoordinateChange_intertwines, energyNumberCoordinates_change]
  rfl

theorem cutoffInteractionForm_change (g Λ : ℝ) (hΛ : 0 < Λ) (P Q : GW.Space)
    (w u : EnergySpace Q) :
    cutoffInteractionForm g Λ hΛ P (energyCoordinateChange P Q w) (energyCoordinateChange P Q u) =
      cutoffInteractionForm g Λ hΛ Q w u :=
  boundedEnergyInteraction_change P Q (cutoffFormFactorL2 g Λ hΛ) w u

end Froehlich
