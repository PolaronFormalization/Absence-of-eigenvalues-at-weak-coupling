import Froehlich.Nodes.UV01CutoffMixed
import Froehlich.Nodes.RS01Sandwich

/-! Cutoff interaction sandwiches use the same auxiliary weights and
fixed reference e as RS01, with its identical uniform mixed constant. -/
noncomputable section
namespace Froehlich

def cutoffAuxiliaryInteractionForm (g Λ : ℝ) (hΛ : 0 < Λ) (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0) :
    GW.Analysis.BoundedForm (HighSectorSpace n) :=
  ((ContinuousLinearMap.compL ℂ (HighSectorSpace n) (EnergySpace (-p)) ℂ).flip
    (auxiliaryEnergyLift n e p he)).comp
      ((cutoffInteractionForm g Λ hΛ (-p)).comp (auxiliaryEnergyLift n e p he))

theorem cutoffAuxiliaryInteractionForm_apply (g Λ : ℝ) (hΛ : 0 < Λ) (n : ℕ) (e : ℝ)
    (p : GW.Space) (he : e ≤ 0) (w u : HighSectorSpace n) :
    cutoffAuxiliaryInteractionForm g Λ hΛ n e p he w u =
      cutoffInteractionForm g Λ hΛ (-p) (auxiliaryEnergyLift n e p he w) (auxiliaryEnergyLift n e p he u) := rfl

def cutoffAuxiliaryInteractionOperator (g Λ : ℝ) (hΛ : 0 < Λ) (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0) :
    HighSectorSpace n →L[ℂ] HighSectorSpace n :=
  formRepresentative (cutoffAuxiliaryInteractionForm g Λ hΛ n e p he)

theorem cutoffAuxiliaryInteractionOperator_selfadjoint (g Λ : ℝ) (hΛ : 0 < Λ)
    (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0) :
    (cutoffAuxiliaryInteractionOperator g Λ hΛ n e p he).adjoint =
      cutoffAuxiliaryInteractionOperator g Λ hΛ n e p he := by
  apply formRepresentative_selfadjoint
  intro w u
  exact cutoffInteractionForm_hermitian g Λ hΛ (-p)
    (auxiliaryEnergyLift n e p he w) (auxiliaryEnergyLift n e p he u)

theorem cutoffAuxiliaryInteractionOperator_norm_le (g Λ : ℝ) (hΛ : 0 < Λ)
    (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0) (hg : |g| ≤ 1) :
    ‖cutoffAuxiliaryInteractionOperator g Λ hΛ n e p he‖ ≤ auxiliaryResolventConstant * |g| := by
  apply formRepresentative_norm_le _ (mul_nonneg auxiliaryResolventConstant_pos.le (abs_nonneg g))
  intro w u
  rw [cutoffAuxiliaryInteractionForm_apply]
  have h := cutoffInteraction_mixed_small g Λ hΛ (-p)
    (auxiliaryEnergyLift n e p he w) (auxiliaryEnergyLift n e p he u) hg
  have hm := mul_le_mul (auxiliaryEnergyLift_norm_le n e p he w) (auxiliaryEnergyLift_norm_le n e p he u)
    (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg 3) (norm_nonneg w))
  calc
    _ ≤ phiMixedConstant * |g| * ‖auxiliaryEnergyLift n e p he w‖ * ‖auxiliaryEnergyLift n e p he u‖ := h
    _ = (phiMixedConstant * |g|)*(‖auxiliaryEnergyLift n e p he w‖ * ‖auxiliaryEnergyLift n e p he u‖) := by ring
    _ ≤ (phiMixedConstant * |g|)*((Real.sqrt 3*‖w‖)*(Real.sqrt 3*‖u‖)) :=
      mul_le_mul_of_nonneg_left hm (mul_nonneg phiMixedConstant_pos.le (abs_nonneg g))
    _ = auxiliaryResolventConstant * |g| * ‖w‖ * ‖u‖ := by
      dsimp only [auxiliaryResolventConstant]
      calc
        _ = (Real.sqrt 3)^2*phiMixedConstant * |g| * ‖w‖ * ‖u‖ := by
          ring
        _ = _ := by simp only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),Submodule.norm_coe]

end Froehlich
