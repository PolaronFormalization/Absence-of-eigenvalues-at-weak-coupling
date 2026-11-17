import Froehlich.Nodes.PT01CoreFieldTesting
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! Every complex L² test on the local set is extended by zero as an
actual global one-particle L² vector, with the literal restricted pairing. -/
noncomputable section
open MeasureTheory
namespace Froehlich
variable (K : Set GW.Space) (hK : MeasurableSet K)

def localScalarTestExtension (chi : Lp ℂ 2 ((volume : Measure GW.Space).restrict K)) : GW.OnePhonon :=
  ((memLp_indicator_iff_restrict hK.nullMeasurableSet).mpr (Lp.memLp chi)).toLp (K.indicator chi)

theorem localScalarTestExtension_ae (chi : Lp ℂ 2 ((volume : Measure GW.Space).restrict K)) :
    localScalarTestExtension K hK chi =ᵐ[volume] K.indicator chi :=
  MemLp.coeFn_toLp _

theorem localScalarTestExtension_restrict_ae (chi : Lp ℂ 2 ((volume : Measure GW.Space).restrict K)) :
    localScalarTestExtension K hK chi =ᵐ[(volume : Measure GW.Space).restrict K] chi := by
  filter_upwards [ae_restrict_of_ae (s := K) (localScalarTestExtension_ae K hK chi),ae_restrict_mem hK]
    with k hk hmem
  rw [hk,Set.indicator_of_mem hmem]

theorem localScalarTestExtension_outside (chi : Lp ℂ 2 ((volume : Measure GW.Space).restrict K)) :
    ∀ᵐ k ∂(volume : Measure GW.Space), k ∉ K → localScalarTestExtension K hK chi k=0 := by
  filter_upwards [localScalarTestExtension_ae K hK chi] with k hk
  intro hnot
  rw [hk,Set.indicator_of_notMem hnot]

theorem localScalarTestExtension_integral_restrict
    (chi : Lp ℂ 2 ((volume : Measure GW.Space).restrict K)) (phi : GW.Space → ℂ) :
    (∫ k in K, (starRingEnd ℂ) (localScalarTestExtension K hK chi k)*phi k)=
      ∫ k, (starRingEnd ℂ) (localScalarTestExtension K hK chi k)*phi k := by
  rw [←integral_indicator hK]
  apply integral_congr_ae
  filter_upwards [localScalarTestExtension_outside K hK chi] with k hk
  by_cases hmem : k ∈ K
  · rw [Set.indicator_of_mem hmem]
  · rw [Set.indicator_of_notMem hmem,hk hmem,map_zero,zero_mul]

end Froehlich
