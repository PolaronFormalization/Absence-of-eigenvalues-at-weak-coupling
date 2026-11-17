import Froehlich.Nodes.UV01SandwichTail
import Froehlich.Nodes.RS01Neumann

/-! Cutoff inverses in the same normalized coordinates, at the same e.
The exact noncommutative inverse identity gives their norm error. -/
noncomputable section
namespace Froehlich

def cutoffAuxiliaryNormalizedOperator (g Λ : ℝ) (hΛ : 0 < Λ) (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0) :
    HighSectorSpace n →L[ℂ] HighSectorSpace n :=
  1 + cutoffAuxiliaryInteractionOperator g Λ hΛ n e p he

def cutoffAuxiliaryNormalizedInverse (g Λ : ℝ) (hΛ : 0 < Λ) (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0)
    (_hg : |g| ≤ 1) (_hsmall : auxiliaryResolventConstant * |g| ≤ 1/2) :
    HighSectorSpace n →L[ℂ] HighSectorSpace n :=
  neumannInverse (-(cutoffAuxiliaryInteractionOperator g Λ hΛ n e p he))

variable (g Λ : ℝ) (hΛ : 0 < Λ) (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0)
    (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant * |g| ≤ 1/2)

theorem cutoffAuxiliaryNormalizedInverse_left :
    cutoffAuxiliaryNormalizedInverse g Λ hΛ n e p he hg hsmall *
      cutoffAuxiliaryNormalizedOperator g Λ hΛ n e p he = 1 := by
  have hn : ‖-(cutoffAuxiliaryInteractionOperator g Λ hΛ n e p he)‖ < 1 :=
    (ContinuousLinearMap.opNorm_neg (cutoffAuxiliaryInteractionOperator g Λ hΛ n e p he)).trans_lt
      (((cutoffAuxiliaryInteractionOperator_norm_le g Λ hΛ n e p he hg).trans hsmall).trans_lt (by norm_num))
  simpa only [cutoffAuxiliaryNormalizedInverse,cutoffAuxiliaryNormalizedOperator,sub_neg_eq_add] using
    neumannInverse_left (-(cutoffAuxiliaryInteractionOperator g Λ hΛ n e p he)) hn

theorem cutoffAuxiliaryNormalizedInverse_right :
    cutoffAuxiliaryNormalizedOperator g Λ hΛ n e p he *
      cutoffAuxiliaryNormalizedInverse g Λ hΛ n e p he hg hsmall = 1 := by
  have hn : ‖-(cutoffAuxiliaryInteractionOperator g Λ hΛ n e p he)‖ < 1 :=
    (ContinuousLinearMap.opNorm_neg (cutoffAuxiliaryInteractionOperator g Λ hΛ n e p he)).trans_lt
      (((cutoffAuxiliaryInteractionOperator_norm_le g Λ hΛ n e p he hg).trans hsmall).trans_lt (by norm_num))
  simpa only [cutoffAuxiliaryNormalizedInverse,cutoffAuxiliaryNormalizedOperator,sub_neg_eq_add] using
    neumannInverse_right (-(cutoffAuxiliaryInteractionOperator g Λ hΛ n e p he)) hn

theorem cutoffAuxiliaryNormalizedInverse_norm_le :
    ‖cutoffAuxiliaryNormalizedInverse g Λ hΛ n e p he hg hsmall‖ ≤ 2 := by
  have hn : ‖-(cutoffAuxiliaryInteractionOperator g Λ hΛ n e p he)‖ ≤ 1/2 :=
    (ContinuousLinearMap.opNorm_neg (cutoffAuxiliaryInteractionOperator g Λ hΛ n e p he)).trans_le
      ((cutoffAuxiliaryInteractionOperator_norm_le g Λ hΛ n e p he hg).trans hsmall)
  have h := neumannInverse_norm_le (-(cutoffAuxiliaryInteractionOperator g Λ hΛ n e p he)) hn
    (by norm_num : (1/2 : ℝ) < 1)
  norm_num at h
  exact h

theorem cutoffAuxiliaryNormalizedInverse_difference :
    cutoffAuxiliaryNormalizedInverse g Λ hΛ n e p he hg hsmall - auxiliaryNormalizedInverse g n e p he hg hsmall =
      cutoffAuxiliaryNormalizedInverse g Λ hΛ n e p he hg hsmall *
        (auxiliaryNormalizedOperator g n e p he-cutoffAuxiliaryNormalizedOperator g Λ hΛ n e p he) *
          auxiliaryNormalizedInverse g n e p he hg hsmall :=
  inverse_sub_identity _ _ _ _ (cutoffAuxiliaryNormalizedInverse_left g Λ hΛ n e p he hg hsmall)
    (auxiliaryNormalizedInverse_right g n e p he hg hsmall)

theorem cutoffAuxiliaryNormalizedInverse_norm_difference :
    ‖cutoffAuxiliaryNormalizedInverse g Λ hΛ n e p he hg hsmall - auxiliaryNormalizedInverse g n e p he hg hsmall‖ ≤
      4*‖cutoffAuxiliaryInteractionOperator g Λ hΛ n e p he-auxiliaryInteractionOperator g n e p he‖ := by
  let R := cutoffAuxiliaryNormalizedInverse g Λ hΛ n e p he hg hsmall
  let Q := auxiliaryNormalizedInverse g n e p he hg hsmall
  let D := auxiliaryNormalizedOperator g n e p he-cutoffAuxiliaryNormalizedOperator g Λ hΛ n e p he
  have hD : D = -(cutoffAuxiliaryInteractionOperator g Λ hΛ n e p he-auxiliaryInteractionOperator g n e p he) := by
    dsimp only [D,auxiliaryNormalizedOperator,cutoffAuxiliaryNormalizedOperator]
    abel
  have hDn : ‖D‖ = ‖cutoffAuxiliaryInteractionOperator g Λ hΛ n e p he-auxiliaryInteractionOperator g n e p he‖ :=
    (congrArg norm hD).trans (ContinuousLinearMap.opNorm_neg _)
  have hR : ‖R‖ ≤ 2 := cutoffAuxiliaryNormalizedInverse_norm_le g Λ hΛ n e p he hg hsmall
  have hQ : ‖Q‖ ≤ 2 := auxiliaryNormalizedInverse_norm_le g n e p he hg hsmall
  have hboth : ‖R‖*‖Q‖ ≤ 4 := by
    have h := mul_le_mul hR hQ (norm_nonneg Q) (by norm_num : (0 : ℝ) ≤ 2)
    norm_num at h
    exact h
  rw [cutoffAuxiliaryNormalizedInverse_difference]
  change ‖(R.comp D).comp Q‖ ≤ _
  calc
    _ ≤ ‖R.comp D‖*‖Q‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (‖R‖*‖D‖)*‖Q‖ := mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg Q)
    _ = (‖R‖*‖Q‖)*‖D‖ := by ring
    _ ≤ 4*‖D‖ := mul_le_mul_of_nonneg_right hboth (norm_nonneg D)
    _ = _ := by rw [hDn]

theorem cutoffAuxiliaryNormalizedInverse_error (hΛone : 1 ≤ Λ) :
    ‖cutoffAuxiliaryNormalizedInverse g Λ hΛ n e p he hg hsmall - auxiliaryNormalizedInverse g n e p he hg hsmall‖ ≤
      12*lyHighConstant * |g| / Real.sqrt Λ := by
  calc
    _ ≤ 4*‖cutoffAuxiliaryInteractionOperator g Λ hΛ n e p he-auxiliaryInteractionOperator g n e p he‖ :=
      cutoffAuxiliaryNormalizedInverse_norm_difference g Λ hΛ n e p he hg hsmall
    _ ≤ 4*(3*lyHighConstant * |g| / Real.sqrt Λ) :=
      mul_le_mul_of_nonneg_left (cutoffAuxiliaryInteractionOperator_error g Λ hΛone n e p he) (by norm_num)
    _ = _ := by ring

end Froehlich
