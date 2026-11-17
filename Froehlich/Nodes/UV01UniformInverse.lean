import Froehlich.Nodes.UV01CommonEnergy
import Froehlich.Nodes.FB02VacuumColumn
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-! Actual uniform operator-norm convergence on one fixed original high
energy graph, for every bounded momentum set. -/
noncomputable section
open Filter
open scoped Topology
namespace Froehlich
variable (n : ℕ) (e : ℝ) (p0 : GW.Space) (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant * |g| ≤ 1/2)

theorem cutoffCommonEnergyInverse_uniform_on_ball (R : ℝ) (hR : 0 ≤ R) :
    TendstoUniformlyOn
      (fun Λ : GW.Operators.PositiveCutoff => fun p : GW.Space => cutoffCommonEnergyInverse n e p0 p hn he g hg hsmall Λ)
      (fun p : GW.Space => singularCommonEnergyInverse n e p0 p hn he g hg hsmall)
      atTop {p : GW.Space | ‖p0-p‖ ≤ R} := by
  letI : PseudoMetricSpace (HighEnergySpace (-p0) n →L[ℂ] HighEnergySpace (-p0) n) :=
    ContinuousLinearMap.toPseudoMetricSpace
  have hr : Tendsto (fun Λ : GW.Operators.PositiveCutoff => (72*(1+R^2))*cutoffTailError g Λ.val)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_apply, mul_zero] using ((cutoffTailError_tendsto g).comp positiveCutoff_coe_tendsto).const_mul (72*(1+R^2))
  have hone : ∀ᶠ Λ : GW.Operators.PositiveCutoff in atTop, 1 ≤ Λ.val := by
    refine eventually_atTop.mpr ⟨⟨1,by norm_num⟩,?_⟩
    intro Λ hΛ
    exact hΛ
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  have hrate := (tendsto_order.1 hr).2 eps heps
  filter_upwards [hone,hrate] with Λ hΛ hsmallrate
  intro p hp
  change ‖-singularCommonEnergyInverse n e p0 p hn he g hg hsmall +
    cutoffCommonEnergyInverse n e p0 p hn he g hg hsmall Λ‖ < eps
  rw [add_comm, ← sub_eq_add_neg]
  have hb := cutoffCommonEnergyInverse_error n e p0 p hn he g hg hsmall Λ hΛ R hR hp
  have hbound : ‖cutoffCommonEnergyInverse n e p0 p hn he g hg hsmall Λ -
      singularCommonEnergyInverse n e p0 p hn he g hg hsmall‖ ≤ (72*(1+R^2))*cutoffTailError g Λ.val := by
    calc
      _ ≤ 72*(1+R^2)*lyHighConstant * |g| / Real.sqrt Λ.val := hb
      _ = _ := by unfold cutoffTailError; ring
  exact hbound.trans_lt hsmallrate

theorem cutoffCommonEnergyInverse_uniform_on_bounded (K : Set GW.Space) (hK : Bornology.IsBounded K) :
    TendstoUniformlyOn
      (fun Λ : GW.Operators.PositiveCutoff => fun p : GW.Space => cutoffCommonEnergyInverse n e p0 p hn he g hg hsmall Λ)
      (fun p : GW.Space => singularCommonEnergyInverse n e p0 p hn he g hg hsmall)
      atTop K := by
  obtain ⟨R,hR,hsub⟩ := hK.subset_closedBall_lt 0 p0
  apply (cutoffCommonEnergyInverse_uniform_on_ball n e p0 hn he g hg hsmall R hR.le).mono
  intro p hp
  have hd : ‖p-p0‖ ≤ R := by
    simpa only [Metric.mem_closedBall,dist_eq_norm] using hsub hp
  change ‖p0-p‖ ≤ R
  simpa only [norm_sub_rev] using hd

end Froehlich
