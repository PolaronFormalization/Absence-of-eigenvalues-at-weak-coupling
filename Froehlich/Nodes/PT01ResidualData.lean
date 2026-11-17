import Froehlich.Nodes.PT01FormContinuity
import Froehlich.Nodes.FC08
import Mathlib.Topology.Metrizable.Basic

set_option autoImplicit false

/-! Actual measurability and a positive bound for the fixed cutoff form
family used to construct the local energy residual. -/
noncomputable section
open MeasureTheory
namespace Froehlich

local instance pt01ResidualDataHighGroup (P : GW.Space) (m : ℕ) :
    NormedAddCommGroup (HighEnergySpace P m) := Submodule.normedAddCommGroup (HighEnergySpace P m)
local instance pt01ResidualDataEndGroup (P : GW.Space) (m : ℕ) :
    NormedAddCommGroup (HighEnergySpace P m →L[ℂ] HighEnergySpace P m) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance pt01ResidualDataEndMetric (P : GW.Space) (m : ℕ) :
    PseudoMetricSpace (HighEnergySpace P m →L[ℂ] HighEnergySpace P m) :=
  ContinuousLinearMap.toPseudoMetricSpace
local instance pt01ResidualDataEndMetrizable (P : GW.Space) (m : ℕ) :
    TopologicalSpace.PseudoMetrizableSpace (HighEnergySpace P m →L[ℂ] HighEnergySpace P m) :=
  @UniformSpace.pseudoMetrizableSpace (HighEnergySpace P m →L[ℂ] HighEnergySpace P m)
    (pt01ResidualDataEndMetric P m).toUniformSpace inferInstance

theorem cutoffResidualFormData (m : ℕ) (e : ℝ) (p : GW.Space) (hm : m ≤ 2)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (Λ : GW.Operators.PositiveCutoff)
    (K : Set GW.Space) (hK : MeasurableSet K) (R : ℝ) (hKR : ∀ k ∈ K, ‖k‖ ≤ R) :
    ∃ M : ℝ, 0 < M ∧
      AEStronglyMeasurable (fun k : GW.Space => (cutoffCommonFormOperator m e 0 (p+k) hm he g Λ : HighEnergySpace 0 m →L[ℂ] HighEnergySpace 0 m))
        ((volume : Measure GW.Space).restrict K) ∧
      ∀ k ∈ K, ‖cutoffCommonFormOperator m e 0 (p+k) hm he g Λ‖ ≤ M := by
  have hb : Bornology.IsBounded ((fun k : GW.Space => p+k) '' K) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨‖p‖+R,?_⟩
    rintro _ ⟨k,hk,rfl⟩
    exact (norm_add_le p k).trans (add_le_add le_rfl (hKR k hk))
  obtain ⟨M,hpos,hbound⟩ := cutoffCommonFormOperator_bounded_on m e 0 hm he g Λ
    ((fun k : GW.Space => p+k) '' K) hb
  refine ⟨M,hpos,?_,?_⟩
  · have hc := (cutoffCommonFormOperator_continuous m e 0 hm he g Λ).comp
      (continuous_const.add continuous_id : Continuous (fun k : GW.Space => p+k))
    exact hc.continuousOn.aestronglyMeasurable hK
  · intro k hk
    exact hbound _ ⟨k,hk,rfl⟩

end Froehlich
