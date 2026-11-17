import Froehlich.Nodes.BA02
import Froehlich.Nodes.DF01
import GW.Operators.FormRepresentation

/-! FA00's general representation is retained GW code. These are exact
applications on its actual record; the concrete fiber record is still GW06 work. -/
noncomputable section
namespace Froehlich
open scoped InnerProductSpace
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem associatedOperator_selfadjoint (d : GW.Operators.CoerciveFormData V H) :
    GW.IsSelfAdjointOperator (GW.Operators.formOperator d) :=
  GW.Operators.formOperator_selfadjoint d

theorem associatedOperator_domain (d : GW.Operators.CoerciveFormData V H) (x : H) :
    x ∈ (GW.Operators.formOperator d).domain ↔
      ∃ u : V, d.embedding u = x ∧ ∃ f : H,
        ∀ w, d.form w u = ⟪d.embedding w, f⟫_ℂ :=
  GW.Operators.formOperator_domain_iff d x
end Froehlich
