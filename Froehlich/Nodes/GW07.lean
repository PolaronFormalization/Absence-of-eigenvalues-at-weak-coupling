import Froehlich.Nodes.FA05

/-! GW07: source realization of the spectrum at the actual GW formOperator.
The energy inverse's three full-domain fields are proved in FA01. -/
namespace Froehlich
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem associated_realSpectrum_preimage (d : GW.Operators.CoerciveFormData V H) :
    realSpectrum (GW.Operators.formOperator d) =
      Complex.ofReal ⁻¹' complexSpectrum (GW.Operators.formOperator d) := rfl

theorem associated_realResolvent_preimage (d : GW.Operators.CoerciveFormData V H) :
    realResolventSet (GW.Operators.formOperator d) =
      Complex.ofReal ⁻¹' complexResolventSet (GW.Operators.formOperator d) := rfl

theorem associated_nonreal_resolvent (d : GW.Operators.CoerciveFormData V H)
    (z : ℂ) (hz : z.im ≠ 0) : z ∈ complexResolventSet (GW.Operators.formOperator d) := by
  exact ⟨GW.Operators.resolvent _ (GW.Operators.formOperator_selfadjoint d) z hz,
    GW.Operators.resolvent_isResolvent _ (GW.Operators.formOperator_selfadjoint d) z hz⟩
end Froehlich
