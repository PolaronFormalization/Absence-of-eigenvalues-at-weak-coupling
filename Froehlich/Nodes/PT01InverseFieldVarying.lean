import Froehlich.Nodes.PT01InverseFieldLimit

set_option autoImplicit false

/-! The actual inverse field limit also accepts varying local L2 sources. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Froehlich

private theorem pt01_varying_input {ι X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (l : Filter ι) (A : ι → X →L[ℂ] Y) (M : ℝ)
    (hA : ∀ i x, ‖A i x‖ ≤ M*‖x‖) (F : ι → X) (f : X) (y : Y)
    (hF : Tendsto F l (𝓝 f)) (hf : Tendsto (fun i => A i f) l (𝓝 y)) :
    Tendsto (fun i => A i (F i)) l (𝓝 y) := by
  have hn : Tendsto (fun i => ‖F i-f‖) l (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.mp hF
  have hb : ∀ i, ‖A i (F i)-A i f‖ ≤ M*‖F i-f‖ := by
    intro i
    rw [← map_sub]
    exact hA i _
  have hm : Tendsto (fun i => M*‖F i-f‖) l (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hn
  have hd : Tendsto (fun i => A i (F i)-A i f) l (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun i => norm_nonneg _) hb hm)
  have h := hd.add hf
  simpa only [zero_add,sub_add_cancel] using h

theorem localCutoffInverseField_tendsto_varying (n : ℕ) (e : ℝ) (p : GW.Space) (hn : n ≤ 2)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (K : Set GW.Space) (hK : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    (F : GW.Operators.PositiveCutoff → Lp (HighSectorSpace n) 2 (volume.restrict K))
    (f : Lp (HighSectorSpace n) 2 (volume.restrict K)) (hF : Tendsto F atTop (𝓝 f)) :
    Tendsto (fun Λ => localCutoffInverseField n e p hn he g hg hs K hK Λ (F Λ)) atTop
      (𝓝 (localSingularInverseField n e p hn he g hg hs K hK hKb f)) := by
  let A := fun Λ : GW.Operators.PositiveCutoff => continuousOperatorFieldAction K hK
    (fun k => cutoffAuxiliaryResolvent n e (p+k) he Λ g hg hs)
    (cutoffInverseField_continuous n e p hn he g hg hs Λ).continuousOn 2
    (fun k _ => cutoffAuxiliaryResolvent_norm_le n e (p+k) he Λ g hg hs)
  apply pt01_varying_input atTop A 2
    (fun Λ x => continuousOperatorFieldAction_norm K hK _ _ _ _ x) F f _ hF
  exact localCutoffInverseField_tendsto n e p hn he g hg hs K hK hKb f

end Froehlich
