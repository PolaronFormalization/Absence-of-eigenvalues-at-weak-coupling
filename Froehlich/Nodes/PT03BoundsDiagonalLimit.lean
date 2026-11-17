import Froehlich.Nodes.PT03BoundsDiagonalContinuity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.Basic

set_option autoImplicit false

/-! Full positive-cutoff-filter dominated convergence for the actual shifted
scalar diagonal. The majorant is Cg² times the ordinary L2 pairing norm. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace Froehlich

local instance pt03DiagonalPositiveOrderTopology : OrderTopology GW.Operators.PositiveCutoff :=
  orderTopology_of_ordConnected (t := Set.Ioi (0 : ℝ))

theorem pt03_positiveCutoff_atTop_countablyGenerated :
    (atTop : Filter GW.Operators.PositiveCutoff).IsCountablyGenerated := by
  infer_instance

local instance pt03DiagonalCutoffFilterCountable :
    (atTop : Filter GW.Operators.PositiveCutoff).IsCountablyGenerated :=
  pt03_positiveCutoff_atTop_countablyGenerated

theorem cutoffThresholdDiagonal_integral_tendsto (e : ℝ)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P : GW.Space) (f h : GW.OnePhonon) :
    Tendsto (fun Lambda : GW.Operators.PositiveCutoff =>
      ∫ q, (starRingEnd ℂ) (f q)*cutoffThresholdDiagonal e he g hg hs Lambda (q-P)*h q) atTop
      (𝓝 (∫ q, (starRingEnd ℂ) (f q)*(-(auxiliarySelfEnergy e (q-P) he g hg hs : ℂ))*h q)) := by
  obtain ⟨C,hC,hBound⟩ := cutoffThresholdDiagonal_uniform
  let B := fun q : GW.Space => (C*g^2)*‖⟪f q,h q⟫_ℂ‖
  have hBI : Integrable B volume := (L2.integrable_inner (𝕜 := ℂ) f h).norm.const_mul (C*g^2)
  apply tendsto_integral_filter_of_dominated_convergence B
  · exact Eventually.of_forall (fun Lambda =>
      (cutoffThresholdDiagonal_shift_integrable e he g hg hs Lambda P f h).aestronglyMeasurable)
  · apply Eventually.of_forall
    intro Lambda
    exact Eventually.of_forall (fun q => by
      simp only [B,norm_mul,RCLike.norm_conj,RCLike.inner_apply']
      have hb := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hBound g e he hg hs Lambda (q-P)) (norm_nonneg (f q)))
        (norm_nonneg (h q))
      exact hb.trans_eq (by ring))
  · exact hBI
  · exact Eventually.of_forall (fun q =>
      (tendsto_const_nhds.mul (cutoffThresholdDiagonal_tendsto e he g hg hs (q-P))).mul tendsto_const_nhds)

end Froehlich
