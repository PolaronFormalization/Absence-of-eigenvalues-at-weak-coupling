import Froehlich.Nodes.PT01CoreLocalTesting
import Froehlich.Nodes.PT01GraphAction
import Froehlich.Nodes.PT01EnergyField
import Froehlich.Nodes.FC08

/-! Bounded tests for the free-graph limit. Only physical shifted outputs
and genuine local energy fields are passed to a limit; never A(Lu_j). -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace Froehlich

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def localL2TestFunctional (K : Set GW.Space)
    (chi : Lp ℂ 2 ((volume : Measure GW.Space).restrict K)) (w : V) :
    Lp V 2 ((volume : Measure GW.Space).restrict K) →L[ℂ] ℂ :=
  (innerSL ℂ chi).comp ((innerSL ℂ w).compLpL 2 ((volume : Measure GW.Space).restrict K))

theorem localL2TestFunctional_integral (K : Set GW.Space)
    (chi : Lp ℂ 2 ((volume : Measure GW.Space).restrict K)) (w : V)
    (F : Lp V 2 ((volume : Measure GW.Space).restrict K)) :
    localL2TestFunctional K chi w F =
      ∫ k in K, (starRingEnd ℂ) (chi k)*⟪w,F k⟫_ℂ := by
  change ⟪chi,(innerSL ℂ w).compLp F⟫_ℂ=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(innerSL ℂ w).coeFn_compLp F] with k hk
  rw [hk]
  simp only [RCLike.inner_apply',innerSL_apply_apply]

theorem localL2TestFunctional_norm_le (K : Set GW.Space)
    (chi : Lp ℂ 2 ((volume : Measure GW.Space).restrict K)) (w : V) :
    ‖localL2TestFunctional K chi w‖ ≤ ‖chi‖*‖w‖ := by
  calc
    _ ≤ ‖innerSL ℂ chi‖*‖(innerSL ℂ w).compLpL 2 ((volume : Measure GW.Space).restrict K)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖innerSL ℂ chi‖*‖innerSL ℂ w‖ := mul_le_mul_of_nonneg_left
      ((innerSL ℂ w).norm_compLpL_le) (innerSL ℂ chi).opNorm_nonneg
    _ = _ := by rw [innerSL_apply_norm,innerSL_apply_norm]

theorem localL2TestFunctional_tendsto {i : Type*} (l : Filter i) (K : Set GW.Space)
    (chi : Lp ℂ 2 ((volume : Measure GW.Space).restrict K)) (w : V)
    (F : i → Lp V 2 ((volume : Measure GW.Space).restrict K))
    (f : Lp V 2 ((volume : Measure GW.Space).restrict K)) (hF : Tendsto F l (𝓝 f)) :
    Tendsto (fun j => ∫ k in K, (starRingEnd ℂ) (chi k)*⟪w,F j k⟫_ℂ) l
      (𝓝 (∫ k in K, (starRingEnd ℂ) (chi k)*⟪w,f k⟫_ℂ)) := by
  have h := ((localL2TestFunctional K chi w).continuous.tendsto f).comp hF
  simpa only [Function.comp_def,localL2TestFunctional_integral] using h

theorem freeGraph_energyField_tendsto (P : GW.Space) (m : ℕ) (K : Set GW.Space) (hK : MeasurableSet K)
    (R : ℝ) (hR : 0 ≤ R) (hKR : ∀ k ∈ K, ‖k‖ ≤ R) (xs : ℕ → OperatorGraphSpace P)
    (x : OperatorGraphSpace P) (hxs : Tendsto xs atTop (𝓝 x)) :
    Tendsto (fun j => restrictedHighEnergyFieldMap P m K hK R hR hKR (xs j)) atTop
      (𝓝 (restrictedHighEnergyFieldMap P m K hK R hR hKR x)) :=
  ((restrictedHighEnergyFieldMap P m K hK R hR hKR).continuous.tendsto x).comp hxs

def cutoffGraphTestRHS (g : ℝ) (P : GW.Space) (n : ℕ) (Lambda : GW.Operators.PositiveCutoff)
    (e : ℝ) (K : Set GW.Space) (hK : MeasurableSet K)
    (chi : Lp ℂ 2 ((volume : Measure GW.Space).restrict K)) (w : boundedMomentumCore) :
    OperatorGraphSpace P →L[ℂ] ℂ :=
  (innerSL ℂ (creationRestriction (localScalarTestExtension K hK chi) (coreNumberLift w))).comp
    (cutoffShiftFreeGraphAction g P n Lambda e) -
    (∫ k in K, (starRingEnd ℂ) (chi k)*cutoffFormFactorL2 g Lambda.val Lambda.property k) •
      ((innerSL ℂ (w : GW.Fock.Carrier)).comp (graphEmbedding P))

theorem cutoffGraphTestRHS_core (g : ℝ) (P : GW.Space) (n : ℕ) (Lambda : GW.Operators.PositiveCutoff)
    (e : ℝ) (K : Set GW.Space) (hK : MeasurableSet K)
    (chi : Lp ℂ 2 ((volume : Measure GW.Space).restrict K)) (w u : boundedMomentumCore) :
    cutoffGraphTestRHS g P n Lambda e K hK chi w (coreFreeGraphLift P u)=
      ⟪creationRestriction (localScalarTestExtension K hK chi) (coreNumberLift w),
        (coreProjectedCutoffShiftAction g P n Lambda e u : GW.Fock.Carrier)⟫_ℂ-
      ∫ k in K, ((starRingEnd ℂ) (chi k)*cutoffFormFactorL2 g Lambda.val Lambda.property k)*
        ⟪(w : GW.Fock.Carrier),(u : GW.Fock.Carrier)⟫_ℂ := by
  change ⟪creationRestriction (localScalarTestExtension K hK chi) (coreNumberLift w),
    cutoffShiftFreeGraphAction g P n Lambda e (coreFreeGraphLift P u)⟫_ℂ-
      (∫ k in K, (starRingEnd ℂ) (chi k)*cutoffFormFactorL2 g Lambda.val Lambda.property k)*
        ⟪(w : GW.Fock.Carrier),graphEmbedding P (coreFreeGraphLift P u)⟫_ℂ=_
  rw [cutoffShiftFreeGraphAction_core,coreFreeGraphLift_embedding,integral_mul_const]

end Froehlich
