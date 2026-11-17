import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! A norm partial derivative from a local coordinate-line integral identity. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology Interval
namespace Froehlich
variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem coordinateLine_hasDerivAt_of_integral
    (F : V → E) (p e : V) (D : ℝ → E)
    (U : Set ℝ) (hU : IsOpen U) (h0 : (0 : ℝ) ∈ U)
    (hD : ContinuousOn D U)
    (hline : ∀ᶠ t in 𝓝 (0 : ℝ),
      F (p+t • e) - F p = ∫ r in (0 : ℝ)..t, D r) :
    HasDerivAt (fun t : ℝ => F (p+t • e)) (D 0) 0 := by
  have hmeas : StronglyMeasurableAtFilter D (𝓝 (0 : ℝ)) :=
    ContinuousOn.stronglyMeasurableAtFilter hU hD 0 h0
  have hcont : ContinuousAt D 0 := hD.continuousAt (hU.mem_nhds h0)
  have hI : HasDerivAt (fun t : ℝ => ∫ r in (0 : ℝ)..t, D r) (D 0) 0 :=
    intervalIntegral.integral_hasDerivAt_right IntervalIntegrable.refl hmeas hcont
  have heq : (fun t : ℝ => F (p+t • e)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t : ℝ => F p + ∫ r in (0 : ℝ)..t, D r) := by
    filter_upwards [hline] with t ht
    calc
      F (p+t • e) = (F (p+t • e) - F p) + F p := (sub_add_cancel _ _).symm
      _ = (∫ r in (0 : ℝ)..t, D r) + F p := congrArg (fun z : E => z + F p) ht
      _ = _ := add_comm _ _
  exact (hI.const_add (F p)).congr_of_eventuallyEq heq

end Froehlich
