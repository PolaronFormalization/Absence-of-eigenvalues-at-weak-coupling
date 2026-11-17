import Froehlich.Nodes.FB01LiebYamazakiCore
import Froehlich.Nodes.FB01Extension

/-! The cutoff-uniform Lieb--Yamazaki inequalities on the actual form domain. -/
noncomputable section
namespace Froehlich

theorem liebYamazaki_cutoff (g Λ : ℝ) (hΛ : 0 < Λ) (P : GW.Space)
    (x : EnergySpace P) (theta : ℝ) (ht : 0 < theta) :
    ‖cutoffInteractionForm g Λ hΛ P x x‖ ≤
      theta * freeEnergy P (energyEmbedding P x) +
        lyRemainderConstant * (g^2/theta + g^4/theta^3) * ‖energyEmbedding P x‖^2 := by
  apply boundedForm_core_diagonal_extension P (cutoffInteractionForm g Λ hΛ P)
    (fun y => theta * freeEnergy P (energyEmbedding P y) +
      lyRemainderConstant * (g^2/theta + g^4/theta^3) * ‖energyEmbedding P y‖^2)
    ((continuous_const.mul (freeEnergy_embedding_continuous P)).add
      (continuous_const.mul ((energyEmbedding P).continuous.norm.pow 2))) _ x
  intro u
  rw [coreEnergyLift_embedding]
  exact liebYamazaki_cutoff_core g Λ hΛ P u theta ht

theorem liebYamazaki_cutoff_small (g Λ : ℝ) (hΛ : 0 < Λ) (P : GW.Space)
    (x : EnergySpace P) (theta : ℝ) (ht : 0 < theta) (hg : |g| ≤ theta) :
    ‖cutoffInteractionForm g Λ hΛ P x x‖ ≤
      theta * freeEnergy P (energyEmbedding P x) +
        (2*lyRemainderConstant*g^2/theta) * ‖energyEmbedding P x‖^2 := by
  apply boundedForm_core_diagonal_extension P (cutoffInteractionForm g Λ hΛ P)
    (fun y => theta * freeEnergy P (energyEmbedding P y) +
      (2*lyRemainderConstant*g^2/theta) * ‖energyEmbedding P y‖^2)
    ((continuous_const.mul (freeEnergy_embedding_continuous P)).add
      (continuous_const.mul ((energyEmbedding P).continuous.norm.pow 2))) _ x
  intro u
  rw [coreEnergyLift_embedding]
  exact liebYamazaki_cutoff_core_small g Λ hΛ P u theta ht hg

end Froehlich
