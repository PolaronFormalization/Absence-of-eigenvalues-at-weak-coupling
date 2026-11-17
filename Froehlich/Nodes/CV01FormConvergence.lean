import Froehlich.Nodes.CV01FormRepresentatives

/-! Actual fixed-graph compressed form representatives converge in norm.
Their cutoff error is independent of the moving momentum. -/
noncomputable section
open Filter
open scoped Topology InnerProductSpace
namespace Froehlich

private theorem operatorNorm_le_of_inner_bound {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (D : H →L[ℂ] H) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ w u, ‖⟪w,D u⟫_ℂ‖ ≤ C*‖w‖*‖u‖) : ‖D‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro u
  have hp := h (D u) u
  rw [inner_self_eq_norm_sq_to_K] at hp
  change ‖((‖D u‖ : ℂ)^2)‖ ≤ C*‖D u‖*‖u‖ at hp
  rw [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_norm] at hp
  by_cases hz : D u=0
  · simp only [hz,norm_zero]
    exact mul_nonneg hC (norm_nonneg u)
  · have hn := norm_pos_iff.mpr hz
    nlinarith

variable (n : ℕ) (e : ℝ) (p0 p : GW.Space) (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ)

theorem commonFormOperator_norm_error (Λ : GW.Operators.PositiveCutoff) (hΛ : 1 ≤ Λ.val) :
    ‖cutoffCommonFormOperator n e p0 p hn he g Λ-singularCommonFormOperator n e p0 p hn he g‖ ≤
      lyHighConstant*|g|/Real.sqrt Λ.val := by
  apply operatorNorm_le_of_inner_bound _ _
    (div_nonneg (mul_nonneg lyHighConstant_pos.le (abs_nonneg g)) (Real.sqrt_nonneg _))
  intro w u
  rw [commonFormOperator_difference_inner n e p0 p hn he g Λ]
  have hb := fb02_tail_mixed g Λ.val hΛ (-p0) (w : EnergySpace (-p0)) (u : EnergySpace (-p0))
  have hr : ‖cutoffInteractionForm g Λ.val Λ.property (-p0) w u-singularInteraction g (-p0) w u‖ =
      ‖(singularInteraction g (-p0)-cutoffInteractionForm g Λ.val Λ.property (-p0)) w u‖ := by
    change ‖cutoffInteractionForm g Λ.val Λ.property (-p0) w u-singularInteraction g (-p0) w u‖ =
      ‖singularInteraction g (-p0) w u-cutoffInteractionForm g Λ.val Λ.property (-p0) w u‖
    exact norm_sub_rev _ _
  rw [hr]
  exact hb

include hn in
theorem commonFormOperator_uniform_on (K : Set GW.Space) :
    TendstoUniformlyOn
      (fun Λ : GW.Operators.PositiveCutoff => fun p : GW.Space => cutoffCommonFormOperator n e p0 p hn he g Λ)
      (fun p : GW.Space => singularCommonFormOperator n e p0 p hn he g) atTop K := by
  letI : PseudoMetricSpace (HighEnergySpace (-p0) n →L[ℂ] HighEnergySpace (-p0) n) :=
    ContinuousLinearMap.toPseudoMetricSpace
  have ht := (cutoffTailError_tendsto g).comp positiveCutoff_coe_tendsto
  change Tendsto (fun Λ : GW.Operators.PositiveCutoff => cutoffTailError g Λ.val) atTop (𝓝 (0 : ℝ)) at ht
  have hlarge : ∀ᶠ Λ : GW.Operators.PositiveCutoff in atTop, 1 ≤ Λ.val :=
    positiveCutoff_coe_tendsto.eventually (eventually_ge_atTop 1)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  have hrate := (tendsto_order.1 ht).2 eps heps
  filter_upwards [hlarge,hrate] with Λ hΛ hrateΛ
  intro p _
  change ‖-singularCommonFormOperator n e p0 p hn he g+
    cutoffCommonFormOperator n e p0 p hn he g Λ‖ < eps
  rw [add_comm,←sub_eq_add_neg]
  exact (commonFormOperator_norm_error n e p0 p hn he g Λ hΛ).trans_lt hrateΛ

end Froehlich
