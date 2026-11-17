import Froehlich.Nodes.PT01InverseFieldLimitTools
import Froehlich.Nodes.PT01InverseContinuity

set_option autoImplicit false

/-! Actual fixed-energy cutoff inverse fields converge in each local L2
space; cutoff and singular families retain the same e. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Froehlich

local instance pt01InverseFieldHighGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n) :=
  Submodule.normedAddCommGroup (HighSectorSpace n)
local instance pt01InverseFieldEndGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance pt01InverseFieldEndPseudoMetric (n : ℕ) : PseudoMetricSpace (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  ContinuousLinearMap.toPseudoMetricSpace
local instance pt01InverseFieldEndPseudoMetrizable (n : ℕ) :
    TopologicalSpace.PseudoMetrizableSpace (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  @UniformSpace.pseudoMetrizableSpace (HighSectorSpace n →L[ℂ] HighSectorSpace n)
    (pt01InverseFieldEndPseudoMetric n).toUniformSpace inferInstance

variable (n : ℕ) (e : ℝ) (p : GW.Space) (hn : n ≤ 2)
  (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
  (hs : auxiliaryResolventConstant*|g| ≤ 1/2)

include hn in
theorem cutoffInverseField_uniform_on_bounded (K : Set GW.Space) (hK : Bornology.IsBounded K) :
    TendstoUniformlyOn
      (fun Λ : GW.Operators.PositiveCutoff => fun k : GW.Space => cutoffAuxiliaryResolvent n e (p+k) he Λ g hg hs)
      (fun k : GW.Space => auxiliaryResolvent n e (p+k) he g hg hs) atTop K := by
  have hb : Bornology.IsBounded ((fun k : GW.Space => p+k) '' K) := by
    obtain ⟨C,hC⟩ := hK.exists_norm_le
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨‖p‖+C,?_⟩
    rintro _ ⟨k,hk,rfl⟩
    exact (norm_add_le p k).trans (add_le_add le_rfl (hC k hk))
  have h := (cutoffAuxiliaryResolvent_uniform_on_bounded n e 0 hn he g hg hs
    ((fun k : GW.Space => p+k) '' K) hb).comp (fun k : GW.Space => p+k)
  simpa only [Function.comp_def] using h.mono (fun k hk => ⟨k,hk,rfl⟩)

include hn in
theorem cutoffInverseField_continuous (Λ : GW.Operators.PositiveCutoff) :
    Continuous (fun k : GW.Space => cutoffAuxiliaryResolvent n e (p+k) he Λ g hg hs) :=
  (cutoffAuxiliaryResolvent_continuous n e hn he g hg hs Λ).comp (continuous_const.add continuous_id)

include hn in
theorem singularInverseField_aestronglyMeasurable (K : Set GW.Space)
    (hK : MeasurableSet K) (hKb : Bornology.IsBounded K) :
    AEStronglyMeasurable (fun k : GW.Space => auxiliaryResolvent n e (p+k) he g hg hs) (volume.restrict K) := by
  apply limitOperatorFamily_aestronglyMeasurable (atTop : Filter ℕ) K hK
    (fun j k => cutoffAuxiliaryResolvent n e (p+k) he (GW.Operators.positiveNatCutoff j) g hg hs)
  · intro j
    exact (cutoffInverseField_continuous n e p hn he g hg hs (GW.Operators.positiveNatCutoff j)).continuousOn
  · intro k hk
    exact ((cutoffInverseField_uniform_on_bounded n e p hn he g hg hs K hKb).tendsto_at hk).comp
      GW.Operators.positiveNatCutoff_tendsto

def localCutoffInverseField (K : Set GW.Space) (hK : MeasurableSet K)
    (Λ : GW.Operators.PositiveCutoff) (F : Lp (HighSectorSpace n) 2 (volume.restrict K)) :
    Lp (HighSectorSpace n) 2 (volume.restrict K) :=
  continuousOperatorFieldAction K hK (fun k => cutoffAuxiliaryResolvent n e (p+k) he Λ g hg hs)
    (cutoffInverseField_continuous n e p hn he g hg hs Λ).continuousOn 2
    (fun k _ => cutoffAuxiliaryResolvent_norm_le n e (p+k) he Λ g hg hs) F

def localSingularInverseField (K : Set GW.Space) (hK : MeasurableSet K) (hKb : Bornology.IsBounded K)
    (F : Lp (HighSectorSpace n) 2 (volume.restrict K)) : Lp (HighSectorSpace n) 2 (volume.restrict K) :=
  operatorFieldValue K hK (fun k => auxiliaryResolvent n e (p+k) he g hg hs)
    (singularInverseField_aestronglyMeasurable n e p hn he g hg hs K hK hKb) 2
    (fun k _ => auxiliaryResolvent_norm_le n e (p+k) he g hg hs) F

theorem localCutoffInverseField_ae (K : Set GW.Space) (hK : MeasurableSet K)
    (Λ : GW.Operators.PositiveCutoff) (F : Lp (HighSectorSpace n) 2 (volume.restrict K)) :
    localCutoffInverseField n e p hn he g hg hs K hK Λ F =ᵐ[volume.restrict K]
      (fun k => cutoffAuxiliaryResolvent n e (p+k) he Λ g hg hs (F k)) :=
  continuousOperatorFieldAction_ae K hK _ _ _ _ F

theorem localSingularInverseField_ae (K : Set GW.Space) (hK : MeasurableSet K) (hKb : Bornology.IsBounded K)
    (F : Lp (HighSectorSpace n) 2 (volume.restrict K)) :
    localSingularInverseField n e p hn he g hg hs K hK hKb F =ᵐ[volume.restrict K]
      (fun k => auxiliaryResolvent n e (p+k) he g hg hs (F k)) :=
  operatorFieldValue_ae K hK _ _ _ _ F

theorem localCutoffInverseField_tendsto (K : Set GW.Space) (hK : MeasurableSet K)
    (hKb : Bornology.IsBounded K) (F : Lp (HighSectorSpace n) 2 (volume.restrict K)) :
    Tendsto (fun Λ : GW.Operators.PositiveCutoff => localCutoffInverseField n e p hn he g hg hs K hK Λ F)
      atTop (𝓝 (localSingularInverseField n e p hn he g hg hs K hK hKb F)) := by
  exact operatorFieldValue_tendsto_of_uniform atTop K hK
    (fun Λ k => cutoffAuxiliaryResolvent n e (p+k) he Λ g hg hs)
    (fun k => auxiliaryResolvent n e (p+k) he g hg hs)
    (fun Λ => (cutoffInverseField_continuous n e p hn he g hg hs Λ).continuousOn.aestronglyMeasurable hK)
    (singularInverseField_aestronglyMeasurable n e p hn he g hg hs K hK hKb) 2 2
    (fun Λ k _ => cutoffAuxiliaryResolvent_norm_le n e (p+k) he Λ g hg hs)
    (fun k _ => auxiliaryResolvent_norm_le n e (p+k) he g hg hs)
    (cutoffInverseField_uniform_on_bounded n e p hn he g hg hs K hKb) F

end Froehlich
