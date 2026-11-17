import Froehlich.Nodes.FB02A

/-! The source's uniform mixed cutoff-to-singular estimate. -/
noncomputable section
namespace Froehlich

theorem singularInteraction_mixed_error (g Λ : ℝ) (hΛ : 0 < Λ) (P : GW.Space)
    (w u : EnergySpace P) :
    ‖(singularInteraction g P - cutoffInteractionForm g Λ hΛ P) w u‖ ≤
      (lyHighConstant * |g| / Real.sqrt Λ) * ‖w‖ * ‖u‖ := by
  have hn : ‖singularInteraction g P - cutoffInteractionForm g Λ hΛ P‖ ≤ cutoffTailError g Λ :=
    (norm_sub_rev (singularInteraction g P) (cutoffInteractionForm g Λ hΛ P)).trans_le
      (cutoffInteraction_limit_error g Λ Λ hΛ hΛ le_rfl P)
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hn (norm_nonneg w)) (norm_nonneg u)
  exact (GW.Analysis.form_bound (singularInteraction g P - cutoffInteractionForm g Λ hΛ P) w u).trans hm

end Froehlich
