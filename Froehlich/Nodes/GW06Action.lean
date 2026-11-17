import Froehlich.Nodes.GW06

/-! Exact full weak-domain and action identities for the actual Hamiltonian. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

def fiberFormCoordinate (g : ℝ) (P : GW.Space) (u : (fiberHamiltonian g P).domain) : EnergySpace P :=
  GW.Operators.operatorFormCoordinate (fiberFormData g P none) u

theorem fiberFormCoordinate_embedding (g : ℝ) (P : GW.Space) (u : (fiberHamiltonian g P).domain) :
    energyEmbedding P (fiberFormCoordinate g P u) = (u : GW.Fock.Carrier) :=
  GW.Operators.operatorFormCoordinate_embedding (fiberFormData g P none) u

theorem fiberHamiltonian_form_identity (g : ℝ) (P : GW.Space)
    (u : (fiberHamiltonian g P).domain) (w : EnergySpace P) :
    freeFiberForm P w (fiberFormCoordinate g P u) +
        singularInteraction g P w (fiberFormCoordinate g P u) =
      ⟪energyEmbedding P w,fiberHamiltonian g P u⟫_ℂ :=
  GW.Operators.formOperator_form_identity (fiberFormData g P none) u w

theorem fiberHamiltonian_domain_of_equation (g : ℝ) (P : GW.Space)
    (u : EnergySpace P) (f : GW.Fock.Carrier)
    (h : ∀ w, freeFiberForm P w u + singularInteraction g P w u = ⟪energyEmbedding P w,f⟫_ℂ) :
    ∃ hmem : energyEmbedding P u ∈ (fiberHamiltonian g P).domain,
      fiberHamiltonian g P ⟨energyEmbedding P u,hmem⟩ = f :=
  GW.Operators.formOperator_domain_of_equation (fiberFormData g P none) u f h

theorem fiberHamiltonian_graph_iff (g : ℝ) (P : GW.Space) (u f : GW.Fock.Carrier) :
    (u,f) ∈ (fiberHamiltonian g P).graph ↔
      ∃ x : EnergySpace P, energyEmbedding P x = u ∧
        ∀ w, freeFiberForm P w x + singularInteraction g P w x = ⟪energyEmbedding P w,f⟫_ℂ := by
  constructor
  · intro h
    obtain ⟨x,hx⟩ := (fiberHamiltonian g P).mem_graph_iff'.mp h
    refine ⟨fiberFormCoordinate g P x, ?_, ?_⟩
    · exact (fiberFormCoordinate_embedding g P x).trans (congrArg Prod.fst hx)
    · intro w
      exact (fiberHamiltonian_form_identity g P x w).trans
        (congrArg (fun z : GW.Fock.Carrier => ⟪energyEmbedding P w,z⟫_ℂ) (congrArg Prod.snd hx))
  · rintro ⟨x,hx,h⟩
    obtain ⟨hm,hv⟩ := fiberHamiltonian_domain_of_equation g P x f h
    exact (fiberHamiltonian g P).mem_graph_iff.mpr ⟨⟨energyEmbedding P x,hm⟩,hx,hv⟩

end Froehlich
