import Froehlich.Nodes.UV01SourceConvergence
import Froehlich.Nodes.UV01SourceTransport

/-! Uniform convergence of the actual source solutions on fixed energy
coordinates. The fixed-reference source is independent of moving momentum. -/
noncomputable section
open Filter
open scoped Topology
namespace Froehlich
variable (n : ℕ) (e : ℝ) (p0 : GW.Space) (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant*|g| ≤ 1/2)

theorem cutoffCommonSourceSolution_uniform_on_ball (R : ℝ) (hR : 0 ≤ R) :
    TendstoUniformlyOn
      (fun Λ : GW.Operators.PositiveCutoff => fun p : GW.Space => cutoffCommonSourceSolution n e p0 p hn he g hg hsmall Λ)
      (fun p : GW.Space => singularCommonSourceSolution n e p0 p hn he g hg hsmall)
      atTop {p : GW.Space | ‖p0-p‖ ≤ R} := by
  let H := singularHighFiberSourceLoad g (-p0) n
  let C := (12*(1+R^2))*Real.sqrt (56*GW.Model.unitBallVolume)*|g| +
    (72*(1+R^2)*lyHighConstant*|g|)*‖H‖
  have htail : Tendsto (fun Λ : GW.Operators.PositiveCutoff => (Real.sqrt Λ.val)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    have hs := (Real.continuous_sqrt.tendsto 0).comp
      ((tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).comp positiveCutoff_coe_tendsto)
    change Tendsto (fun Λ : GW.Operators.PositiveCutoff => Real.sqrt (Λ.val⁻¹)) atTop (𝓝 (Real.sqrt (0 : ℝ))) at hs
    simpa only [Real.sqrt_inv,Real.sqrt_zero] using hs
  have hrate : Tendsto (fun Λ : GW.Operators.PositiveCutoff => C*(Real.sqrt Λ.val)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using htail.const_mul C
  have hlarge : ∀ᶠ Λ : GW.Operators.PositiveCutoff in atTop, max 1 (2*‖p0‖) ≤ Λ.val :=
    positiveCutoff_coe_tendsto.eventually (eventually_ge_atTop _)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  have hsmallrate := (tendsto_order.1 hrate).2 eps heps
  filter_upwards [hlarge,hsmallrate] with Λ hΛ hrateΛ
  intro p hp
  rw [dist_comm,dist_eq_norm]
  let Q := cutoffCommonEnergyInverse n e p0 p hn he g hg hsmall Λ
  let T := singularCommonEnergyInverse n e p0 p hn he g hg hsmall
  let F := cutoffCommonSourceLoad g p0 p n Λ.val
  let z := loadRiesz F
  let w := loadRiesz H
  have hid : cutoffCommonSourceSolution n e p0 p hn he g hg hsmall Λ -
      singularCommonSourceSolution n e p0 p hn he g hg hsmall = Q (z-w)+(Q-T) w := by
    change Q z-T (loadRiesz (singularCommonSourceLoad g p0 p n)) = _
    rw [singularCommonSourceLoad_eq,Q.map_sub]
    change Q z-T w = (Q z-Q w)+(Q w-T w)
    abel
  have hz : ‖z-w‖ = ‖F-H‖ := by
    have hmap := (loadRieszLinearIsometry (V := HighEnergySpace (-p0) n)).map_sub F H
    change loadRiesz (F-H) = z-w at hmap
    rw [←hmap]
    exact loadRiesz_norm (F-H)
  have hF : ‖F-H‖ ≤ Real.sqrt (56*GW.Model.unitBallVolume)*|g|/Real.sqrt Λ.val := by
    have hh := cutoffCommonSourceLoad_reference_error g Λ.val p0 p n hΛ
    rw [singularCommonSourceLoad_eq] at hh
    exact hh
  have hb : ‖cutoffCommonSourceSolution n e p0 p hn he g hg hsmall Λ -
      singularCommonSourceSolution n e p0 p hn he g hg hsmall‖ ≤ C*(Real.sqrt Λ.val)⁻¹ := by
    rw [hid]
    calc
      _ ≤ ‖Q (z-w)‖+‖(Q-T) w‖ := norm_add_le _ _
      _ ≤ ‖Q‖*‖z-w‖+‖Q-T‖*‖w‖ := add_le_add (Q.le_opNorm _) ((Q-T).le_opNorm _)
      _ = ‖Q‖*‖F-H‖+‖Q-T‖*‖H‖ := by rw [hz,loadRiesz_norm]
      _ ≤ (12*(1+R^2))*(Real.sqrt (56*GW.Model.unitBallVolume)*|g|/Real.sqrt Λ.val) +
          (72*(1+R^2)*lyHighConstant*|g|/Real.sqrt Λ.val)*‖H‖ := add_le_add
        (mul_le_mul (cutoffCommonEnergyInverse_norm_le n e p hn he g hg hsmall p0 Λ R hR hp)
          hF (norm_nonneg _) (by positivity))
        (mul_le_mul_of_nonneg_right
          (cutoffCommonEnergyInverse_error n e p0 p hn he g hg hsmall Λ ((le_max_left _ _).trans hΛ) R hR hp)
          (norm_nonneg H))
      _ = _ := by dsimp only [C]; ring
  exact hb.trans_lt hrateΛ

end Froehlich
