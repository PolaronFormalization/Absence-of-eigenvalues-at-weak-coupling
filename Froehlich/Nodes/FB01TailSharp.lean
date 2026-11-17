import Froehlich.Nodes.FB01KineticIdentityFull
import Froehlich.Nodes.FB01HighBound

/-! The sharp finite-tail product estimate on the full actual form domain. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
namespace Froehlich

theorem lyHighForm_energy_sharp (g L Λ : ℝ) (hL : 0 < L) (hLΛ : L ≤ Λ)
    (P : GW.Space) (x : EnergySpace P) :
    ‖cutoffInteractionForm g Λ (hL.trans_le hLΛ) P x x - cutoffInteractionForm g L hL P x x‖ ≤
      lyHighConstant * |g| / Real.sqrt L * energyKineticNorm P x * ‖energyNumberCoordinates P x‖ := by
  apply boundedForm_core_diagonal_extension P
    (cutoffInteractionForm g Λ (hL.trans_le hLΛ) P - cutoffInteractionForm g L hL P)
    (fun y => lyHighConstant * |g| / Real.sqrt L * energyKineticNorm P y * ‖energyNumberCoordinates P y‖)
    ((continuous_const.mul (energyKineticNorm_continuous P)).mul (energyNumberCoordinates P).continuous.norm) _ x
  intro u
  rw [energyKineticNorm_core,coreEnergyNumberCoordinates_eq]
  exact lyHighForm_core_bound g L Λ hL hLΛ P u

theorem lyHighForm_energy_sharp_actual (g L Λ : ℝ) (hL : 0 < L) (hLΛ : L ≤ Λ)
    (P : GW.Space) (x : EnergySpace P) :
    ‖cutoffInteractionForm g Λ (hL.trans_le hLΛ) P x x - cutoffInteractionForm g L hL P x x‖ ≤
      lyHighConstant * |g| / Real.sqrt L * energyKineticNorm P x *
        ‖GW.Fock.shiftedNumberPower GW.Fock.Sector (1/2)
          (GW.Fock.shiftedNumberInput GW.Fock.Sector (1/2) (by positivity)
            (numberFormRootInput (energyNumberCoordinates P x)))‖ := by
  rw [numberForm_shiftedRoot_norm]
  exact lyHighForm_energy_sharp g L Λ hL hLΛ P x

end Froehlich
