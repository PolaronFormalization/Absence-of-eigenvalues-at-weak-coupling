import Froehlich.Nodes.FB01Extension
import Froehlich.Nodes.FB01HighBound

/-! Uniform tail control extended in the genuine energy norm. -/
noncomputable section
namespace Froehlich

theorem lyHighForm_energy_diagonal_bound (g L Λ : ℝ) (hL : 0 < L) (hLΛ : L ≤ Λ)
    (P : GW.Space) (x : EnergySpace P) :
    ‖cutoffInteractionForm g Λ (hL.trans_le hLΛ) P x x -
      cutoffInteractionForm g L hL P x x‖ ≤
      (lyHighConstant * |g| / Real.sqrt L) * ‖x‖^2 := by
  let C := lyHighConstant * |g| / Real.sqrt L
  have hC : 0 ≤ C := div_nonneg (mul_nonneg lyHighConstant_pos.le (abs_nonneg g))
    (Real.sqrt_nonneg L)
  apply boundedForm_core_diagonal_extension P
    (cutoffInteractionForm g Λ (hL.trans_le hLΛ) P - cutoffInteractionForm g L hL P)
    (fun y => C * ‖y‖^2) (continuous_const.mul (continuous_norm.pow 2)) _ x
  intro u
  have hn : ‖coreNumberLift u‖ ≤ ‖coreEnergyLift P u‖ := by
    rw [← coreEnergyNumberCoordinates_eq P u]
    exact energyNumberCoordinates_norm_le P _
  have he := energyEmbedding_norm_identity P (coreEnergyLift P u)
  rw [coreEnergyLift_embedding] at he
  have hd : (∑ j : Fin 3, ‖coreKineticComponent P j u‖^2) ≤ ‖coreEnergyLift P u‖^2 :=
    (coreKineticComponent_bound P u).trans (by nlinarith [sq_nonneg ‖(u : GW.Fock.Carrier)‖])
  have hs : Real.sqrt (∑ j : Fin 3, ‖coreKineticComponent P j u‖^2) ≤ ‖coreEnergyLift P u‖ := by
    exact (Real.sqrt_le_sqrt hd).trans_eq (Real.sqrt_sq (norm_nonneg _))
  have hp : Real.sqrt (∑ j : Fin 3, ‖coreKineticComponent P j u‖^2) * ‖coreNumberLift u‖ ≤
      ‖coreEnergyLift P u‖^2 := by
    exact (mul_le_mul hs hn (norm_nonneg _) (norm_nonneg _)).trans_eq (pow_two _).symm
  change ‖cutoffInteractionForm g Λ (hL.trans_le hLΛ) P (coreEnergyLift P u) (coreEnergyLift P u) -
    cutoffInteractionForm g L hL P (coreEnergyLift P u) (coreEnergyLift P u)‖ ≤ _
  exact (lyHighForm_core_bound g L Λ hL hLΛ P u).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp hC)

end Froehlich
