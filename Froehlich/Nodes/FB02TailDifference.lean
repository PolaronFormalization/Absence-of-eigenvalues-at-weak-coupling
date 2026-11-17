import Froehlich.Nodes.FB01TailNorm

/-! Uniform differences of actual finite cutoff forms. -/
noncomputable section
open Filter
open scoped Topology
namespace Froehlich

def cutoffTailError (g R : ℝ) : ℝ := lyHighConstant * |g| / Real.sqrt R

theorem cutoffTailError_nonneg (g R : ℝ) : 0 ≤ cutoffTailError g R :=
  div_nonneg (mul_nonneg lyHighConstant_pos.le (abs_nonneg g)) (Real.sqrt_nonneg R)

theorem cutoffTailError_tendsto (g : ℝ) : Tendsto (cutoffTailError g) atTop (𝓝 0) :=
  Real.tendsto_sqrt_atTop.const_div_atTop _

theorem cutoffInteraction_difference_norm (g R Λ Λ' : ℝ) (hR : 0 < R)
    (hΛ : 0 < Λ) (hΛ' : 0 < Λ') (hRΛ : R ≤ Λ) (hRΛ' : R ≤ Λ') (P : GW.Space) :
    ‖cutoffInteractionForm g Λ hΛ P - cutoffInteractionForm g Λ' hΛ' P‖ ≤ cutoffTailError g R := by
  have hc : 0 ≤ lyHighConstant * |g| := mul_nonneg lyHighConstant_pos.le (abs_nonneg g)
  by_cases h : Λ ≤ Λ'
  · calc
      _ = ‖cutoffInteractionForm g Λ' hΛ' P - cutoffInteractionForm g Λ hΛ P‖ :=
        norm_sub_rev (cutoffInteractionForm g Λ hΛ P) (cutoffInteractionForm g Λ' hΛ' P)
      _ ≤ lyHighConstant * |g| / Real.sqrt Λ := cutoffInteraction_tail_norm g Λ Λ' hΛ h P
      _ ≤ cutoffTailError g R :=
        div_le_div_of_nonneg_left hc (Real.sqrt_pos.mpr hR) (Real.sqrt_le_sqrt hRΛ)
  · have h' : Λ' ≤ Λ := le_of_not_ge h
    apply (cutoffInteraction_tail_norm g Λ' Λ hΛ' h' P).trans
    exact div_le_div_of_nonneg_left hc (Real.sqrt_pos.mpr hR) (Real.sqrt_le_sqrt hRΛ')

theorem cutoffInteraction_difference_diagonal (g R Λ Λ' : ℝ) (hR : 0 < R)
    (hΛ : 0 < Λ) (hΛ' : 0 < Λ') (hRΛ : R ≤ Λ) (hRΛ' : R ≤ Λ') (P : GW.Space)
    (u : EnergySpace P) :
    ‖(cutoffInteractionForm g Λ hΛ P - cutoffInteractionForm g Λ' hΛ' P) u u‖ ≤
      cutoffTailError g R * ‖u‖^2 := by
  have h := GW.Analysis.form_bound (cutoffInteractionForm g Λ hΛ P - cutoffInteractionForm g Λ' hΛ' P) u u
  have hb := cutoffInteraction_difference_norm g R Λ Λ' hR hΛ hΛ' hRΛ hRΛ' P
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hb (norm_nonneg u)) (norm_nonneg u)
  exact h.trans (hm.trans_eq (by ring))

end Froehlich
