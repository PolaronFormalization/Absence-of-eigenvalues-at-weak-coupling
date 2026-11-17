import Froehlich.Nodes.GW06

/-! Exact specialization of retained associated-operator uniqueness. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem fiberHamiltonian_unique (g : ℝ) (P : GW.Space)
    (L : GW.Fock.Carrier →ₗ.[ℂ] GW.Fock.Carrier) (hL : GW.IsSelfAdjointOperator L)
    (hform : ∀ x : L.domain, ∃ u : EnergySpace P, energyEmbedding P u = (x : GW.Fock.Carrier) ∧
      ∀ w, freeFiberForm P w u + singularInteraction g P w u = ⟪energyEmbedding P w,L x⟫_ℂ) :
    L = fiberHamiltonian g P :=
  GW.Operators.formOperator_unique (fiberFormData g P none) L hL hform

end Froehlich
