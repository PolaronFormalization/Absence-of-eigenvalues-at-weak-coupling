import Froehlich.Nodes.RS01Sandwich

/-! BA02's genuine Banach-ring Neumann inverse of I+T, with source
norm two and positivity. The smallness hypotheses precede its definition. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

def auxiliaryNormalizedOperator (g : ℝ) (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0) :
    HighSectorSpace n →L[ℂ] HighSectorSpace n :=
  1 + auxiliaryInteractionOperator g n e p he

def auxiliaryNormalizedInverse (g : ℝ) (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0)
    (_hg : |g| ≤ 1) (_hsmall : auxiliaryResolventConstant * |g| ≤ 1/2) :
    HighSectorSpace n →L[ℂ] HighSectorSpace n :=
  neumannInverse (-(auxiliaryInteractionOperator g n e p he))

theorem auxiliaryInteractionOperator_norm_half (g : ℝ) (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0)
    (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant * |g| ≤ 1/2) :
    ‖auxiliaryInteractionOperator g n e p he‖ ≤ 1/2 :=
  (auxiliaryInteractionOperator_norm_le g n e p he hg).trans hsmall

theorem auxiliaryNormalizedOperator_selfadjoint (g : ℝ) (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0) :
    (auxiliaryNormalizedOperator g n e p he).adjoint = auxiliaryNormalizedOperator g n e p he := by
  simp only [auxiliaryNormalizedOperator,map_add,ContinuousLinearMap.adjoint_one,
    auxiliaryInteractionOperator_selfadjoint]

theorem auxiliaryNormalizedInverse_left (g : ℝ) (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0)
    (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant * |g| ≤ 1/2) :
    auxiliaryNormalizedInverse g n e p he hg hsmall * auxiliaryNormalizedOperator g n e p he = 1 := by
  have hn : ‖-(auxiliaryInteractionOperator g n e p he)‖ < 1 := by
    exact (ContinuousLinearMap.opNorm_neg (auxiliaryInteractionOperator g n e p he)).trans_lt
      ((auxiliaryInteractionOperator_norm_half g n e p he hg hsmall).trans_lt (by norm_num))
  simpa only [auxiliaryNormalizedInverse,auxiliaryNormalizedOperator,sub_neg_eq_add] using
    neumannInverse_left (-(auxiliaryInteractionOperator g n e p he)) hn

theorem auxiliaryNormalizedInverse_right (g : ℝ) (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0)
    (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant * |g| ≤ 1/2) :
    auxiliaryNormalizedOperator g n e p he * auxiliaryNormalizedInverse g n e p he hg hsmall = 1 := by
  have hn : ‖-(auxiliaryInteractionOperator g n e p he)‖ < 1 := by
    exact (ContinuousLinearMap.opNorm_neg (auxiliaryInteractionOperator g n e p he)).trans_lt
      ((auxiliaryInteractionOperator_norm_half g n e p he hg hsmall).trans_lt (by norm_num))
  simpa only [auxiliaryNormalizedInverse,auxiliaryNormalizedOperator,sub_neg_eq_add] using
    neumannInverse_right (-(auxiliaryInteractionOperator g n e p he)) hn

theorem auxiliaryNormalizedInverse_norm_le (g : ℝ) (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0)
    (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant * |g| ≤ 1/2) :
    ‖auxiliaryNormalizedInverse g n e p he hg hsmall‖ ≤ 2 := by
  have hn : ‖-(auxiliaryInteractionOperator g n e p he)‖ ≤ 1/2 := by
    exact (ContinuousLinearMap.opNorm_neg (auxiliaryInteractionOperator g n e p he)).trans_le
      (auxiliaryInteractionOperator_norm_half g n e p he hg hsmall)
  have h := neumannInverse_norm_le (-(auxiliaryInteractionOperator g n e p he)) hn (by norm_num : (1/2 : ℝ) < 1)
  norm_num at h
  exact h

theorem auxiliaryNormalizedOperator_lower (g : ℝ) (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0)
    (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant * |g| ≤ 1/2) (u : HighSectorSpace n) :
    (1/2 : ℝ)*‖u‖^2 ≤ (⟪u,auxiliaryNormalizedOperator g n e p he u⟫_ℂ).re := by
  have hT := auxiliaryInteractionOperator_norm_half g n e p he hg hsmall
  have hTu : ‖auxiliaryInteractionOperator g n e p he u‖ ≤ (1/2 : ℝ)*‖u‖ :=
    ((auxiliaryInteractionOperator g n e p he).le_opNorm u).trans
      (mul_le_mul_of_nonneg_right hT (norm_nonneg u))
  have hab := (Complex.abs_re_le_norm (⟪u,auxiliaryInteractionOperator g n e p he u⟫_ℂ)).trans
    (norm_inner_le_norm (𝕜 := ℂ) u (auxiliaryInteractionOperator g n e p he u))
  have hl := neg_le_of_abs_le hab
  have hi : (⟪u,u⟫_ℂ).re = ‖u‖^2 := by
    simpa only [RCLike.re_eq_complex_re] using (norm_sq_eq_re_inner (𝕜 := ℂ) u).symm
  simp only [auxiliaryNormalizedOperator,ContinuousLinearMap.add_apply,ContinuousLinearMap.one_apply,
    inner_add_right,Complex.add_re,hi]
  nlinarith [norm_nonneg u]

theorem auxiliaryNormalizedInverse_nonnegative (g : ℝ) (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0)
    (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant * |g| ≤ 1/2) (z : HighSectorSpace n) :
    0 ≤ (⟪z,auxiliaryNormalizedInverse g n e p he hg hsmall z⟫_ℂ).re := by
  apply inverse_nonnegative _ _ (auxiliaryNormalizedOperator_selfadjoint g n e p he)
  · intro u
    exact congrArg (fun T : HighSectorSpace n →L[ℂ] HighSectorSpace n => T u)
      (auxiliaryNormalizedInverse_right g n e p he hg hsmall)
  · intro u
    exact (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) (sq_nonneg ‖u‖)).trans
      (auxiliaryNormalizedOperator_lower g n e p he hg hsmall u)

end Froehlich
