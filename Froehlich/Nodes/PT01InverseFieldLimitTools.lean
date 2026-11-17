import Froehlich.Nodes.FC08
import Mathlib.Topology.MetricSpace.Pseudo.Basic

set_option autoImplicit false

/-! Uniform operator-norm convergence acts in the actual local L2 norm. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Froehlich
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem operatorFieldValue_sub_norm_le (K : Set GW.Space) (hK : MeasurableSet K)
    (T S : GW.Space → V →L[ℂ] W)
    (hT : AEStronglyMeasurable T (volume.restrict K))
    (hS : AEStronglyMeasurable S (volume.restrict K)) (M N delta : ℝ)
    (hM : ∀ k ∈ K, ‖T k‖ ≤ M) (hN : ∀ k ∈ K, ‖S k‖ ≤ N)
    (hd : ∀ k ∈ K, ‖T k-S k‖ ≤ delta) (F : Lp V 2 (volume.restrict K)) :
    ‖operatorFieldValue K hK T hT M hM F-operatorFieldValue K hK S hS N hN F‖ ≤ delta*‖F‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [operatorFieldValue_ae K hK T hT M hM F,
    operatorFieldValue_ae K hK S hS N hN F,
    Lp.coeFn_sub (operatorFieldValue K hK T hT M hM F) (operatorFieldValue K hK S hS N hN F),
    self_mem_ae_restrict hK] with k ht hs hout hk
  simp only [Pi.sub_apply] at hout
  rw [hout,ht,hs]
  change ‖(T k-S k) (F k)‖ ≤ _
  exact ((T k-S k).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hd k hk) (norm_nonneg _))

theorem operatorFieldValue_tendsto_of_uniform {ι : Type*} (l : Filter ι)
    (K : Set GW.Space) (hK : MeasurableSet K)
    (T : ι → GW.Space → V →L[ℂ] W) (S : GW.Space → V →L[ℂ] W)
    (hT : ∀ i, AEStronglyMeasurable (T i) (volume.restrict K))
    (hS : AEStronglyMeasurable S (volume.restrict K)) (M N : ℝ)
    (hM : ∀ i k, k ∈ K → ‖T i k‖ ≤ M) (hN : ∀ k ∈ K, ‖S k‖ ≤ N)
    (hlim : TendstoUniformlyOn T S l K) (F : Lp V 2 (volume.restrict K)) :
    Tendsto (fun i => operatorFieldValue K hK (T i) (hT i) M (hM i) F) l
      (𝓝 (operatorFieldValue K hK S hS N hN F)) := by
  apply Metric.tendsto_nhds.mpr
  intro epsilon he
  let delta := epsilon/(‖F‖+1)
  have hd : 0 < delta := div_pos he (by positivity)
  have hu := (Metric.tendstoUniformlyOn_iff.mp hlim) delta hd
  filter_upwards [hu] with i hi
  have hbound (k : GW.Space) (hk : k ∈ K) : ‖T i k-S k‖ ≤ delta := by
    have h := hi k hk
    rw [dist_comm,dist_eq_norm] at h
    exact h.le
  have hb := operatorFieldValue_sub_norm_le K hK (T i) S (hT i) hS M N delta (hM i) hN hbound F
  rw [dist_eq_norm]
  refine hb.trans_lt ?_
  have hEq : delta*(‖F‖+1)=epsilon := div_mul_cancel₀ epsilon (ne_of_gt (by positivity : 0 < ‖F‖+1))
  nlinarith

end Froehlich
