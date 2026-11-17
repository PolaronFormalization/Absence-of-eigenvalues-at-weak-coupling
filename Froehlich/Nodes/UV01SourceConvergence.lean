import Froehlich.Nodes.UV01SourceError
import Froehlich.Nodes.FB02VacuumColumn

/-! Genuine source-solution convergence in a fixed original energy graph.
The cutoff energy parameter remains the same independent number e. -/
noncomputable section
open Filter
open scoped Topology
namespace Froehlich
variable (n : ℕ) (e : ℝ) (p0 p : GW.Space) (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant * |g| ≤ 1/2)

theorem cutoffCommonSourceSolution_tendsto :
    Tendsto (fun Λ : GW.Operators.PositiveCutoff => cutoffCommonSourceSolution n e p0 p hn he g hg hsmall Λ)
      atTop (𝓝 (singularCommonSourceSolution n e p0 p hn he g hg hsmall)) := by
  let R := ‖p0-p‖
  let S := ‖p‖
  let C := (12*(1+R^2))*(Real.sqrt (56*GW.Model.unitBallVolume)*|g| *
      momentumChangeConstant (-p) (-p0)) +
    (72*(1+R^2)*lyHighConstant*|g|)*‖singularCommonSourceLoad g p0 p n‖
  have htail : Tendsto (fun Λ : GW.Operators.PositiveCutoff => (Real.sqrt Λ.val)⁻¹)
      atTop (𝓝 (0 : ℝ)) := by
    have hi := (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).comp
      positiveCutoff_coe_tendsto
    have hs := (Real.continuous_sqrt.tendsto 0).comp hi
    change Tendsto (fun Λ : GW.Operators.PositiveCutoff => Real.sqrt (Λ.val⁻¹))
      atTop (𝓝 (Real.sqrt (0 : ℝ))) at hs
    simpa only [Real.sqrt_inv,Real.sqrt_zero] using hs
  have hrate : Tendsto (fun Λ : GW.Operators.PositiveCutoff => C*(Real.sqrt Λ.val)⁻¹)
      atTop (𝓝 (0 : ℝ)) := by simpa only [mul_zero] using htail.const_mul C
  have hlarge : ∀ᶠ Λ : GW.Operators.PositiveCutoff in atTop, max 1 (2*S) ≤ Λ.val :=
    positiveCutoff_coe_tendsto.eventually (eventually_ge_atTop (max 1 (2*S)))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun Λ => norm_nonneg
    (cutoffCommonSourceSolution n e p0 p hn he g hg hsmall Λ -
      singularCommonSourceSolution n e p0 p hn he g hg hsmall))) _ hrate
  filter_upwards [hlarge] with Λ hΛ
  have hb := cutoffCommonSourceSolution_error n e p0 p hn he g hg hsmall Λ
    ((le_max_left 1 (2*S)).trans hΛ) R S (norm_nonneg _) le_rfl le_rfl hΛ
  calc
    _ ≤ _ := hb
    _ = C*(Real.sqrt Λ.val)⁻¹ := by dsimp only [C]; ring

end Froehlich
