import Froehlich.Nodes.UV01Sandwich

/-! Uniform cutoff-to-singular sandwich error in the very same physical
coordinates and at the same reference e. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem cutoffAuxiliaryInteractionOperator_error (g Λ : ℝ) (hΛ : 1 ≤ Λ)
    (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0) :
    ‖cutoffAuxiliaryInteractionOperator g Λ (zero_lt_one.trans_le hΛ) n e p he -
      auxiliaryInteractionOperator g n e p he‖ ≤ 3*lyHighConstant * |g| / Real.sqrt Λ := by
  let A := cutoffAuxiliaryInteractionForm g Λ (zero_lt_one.trans_le hΛ) n e p he
  let B := auxiliaryInteractionForm g n e p he
  have hrep : cutoffAuxiliaryInteractionOperator g Λ (zero_lt_one.trans_le hΛ) n e p he -
      auxiliaryInteractionOperator g n e p he = formRepresentative (A-B) := by
    apply formRepresentative_unique
    intro w u
    change A w u-B w u = ⟪w,formRepresentative A u-formRepresentative B u⟫_ℂ
    rw [inner_sub_right,← formRepresentative_spec,← formRepresentative_spec]
  rw [hrep]
  let theta := lyHighConstant * |g| / Real.sqrt Λ
  have htheta : 0 ≤ theta := div_nonneg (mul_nonneg lyHighConstant_pos.le (abs_nonneg g)) (Real.sqrt_nonneg _)
  have hC : 3*theta = 3*lyHighConstant * |g| / Real.sqrt Λ := by dsimp only [theta]; ring
  rw [← hC]
  apply formRepresentative_norm_le _ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) htheta)
  intro w u
  change ‖cutoffInteractionForm g Λ (zero_lt_one.trans_le hΛ) (-p)
      (auxiliaryEnergyLift n e p he w) (auxiliaryEnergyLift n e p he u) -
      singularInteraction g (-p) (auxiliaryEnergyLift n e p he w) (auxiliaryEnergyLift n e p he u)‖ ≤ _
  have ht := fb02_tail_mixed g Λ hΛ (-p) (auxiliaryEnergyLift n e p he w) (auxiliaryEnergyLift n e p he u)
  change ‖singularInteraction g (-p) (auxiliaryEnergyLift n e p he w) (auxiliaryEnergyLift n e p he u) -
      cutoffInteractionForm g Λ (zero_lt_one.trans_le hΛ) (-p)
        (auxiliaryEnergyLift n e p he w) (auxiliaryEnergyLift n e p he u)‖ ≤
      theta*‖auxiliaryEnergyLift n e p he w‖ * ‖auxiliaryEnergyLift n e p he u‖ at ht
  rw [norm_sub_rev]
  have hm := mul_le_mul (auxiliaryEnergyLift_norm_le n e p he w) (auxiliaryEnergyLift_norm_le n e p he u)
    (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg 3) (norm_nonneg w))
  calc
    _ ≤ theta*‖auxiliaryEnergyLift n e p he w‖ * ‖auxiliaryEnergyLift n e p he u‖ := ht
    _ = theta*(‖auxiliaryEnergyLift n e p he w‖ * ‖auxiliaryEnergyLift n e p he u‖) := by ring
    _ ≤ theta*((Real.sqrt 3*‖w‖)*(Real.sqrt 3*‖u‖)) := mul_le_mul_of_nonneg_left hm htheta
    _ = (3*theta)*‖w‖ * ‖u‖ := by
      calc
        _ = (Real.sqrt 3)^2*theta*‖w‖ * ‖u‖ := by ring
        _ = _ := by simp only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),Submodule.norm_coe]

end Froehlich
