import Froehlich.Nodes.UV02DomainEquality

/-! The literal cutoff action on the actual free maximal domain, in its
canonical original-energy coordinate. -/
noncomputable section
namespace Froehlich

def freeDomainEnergyCoordinate (P : GW.Space) (u : (freeFiberOperator P).domain) : EnergySpace P :=
  (energyEmbedding P).adjoint (freeFiberOperator P u+(u : GW.Fock.Carrier))

theorem freeDomainEnergyCoordinate_physical (P : GW.Space) (u : (freeFiberOperator P).domain) :
    energyEmbedding P (freeDomainEnergyCoordinate P u)=(u : GW.Fock.Carrier) :=
  freeFiberOperator_graph_energyLift P u (freeFiberOperator P u) ((freeFiberOperator P).mem_graph u)

theorem cutoff_freeDomain_action (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff)
    (u : (freeFiberOperator P).domain) :
    cutoffHamiltonian g P Λ ⟨(u : GW.Fock.Carrier),freeDomain_subset_cutoffDomain g P Λ u.property⟩=
      freeFiberOperator P u+energySmearedField P (cutoffFormFactorL2 g Λ.val Λ.property)
        (freeDomainEnergyCoordinate P u) := by
  obtain ⟨x,hx,hgraph⟩ := freeGraph_cutoffGraph g P Λ u (freeFiberOperator P u)
    ((freeFiberOperator P).mem_graph u)
  have hxeq : x=freeDomainEnergyCoordinate P u := by
    apply energyEmbedding_injective P
    rw [hx,freeDomainEnergyCoordinate_physical]
  rw [hxeq] at hgraph
  exact (cutoffHamiltonian g P Λ).mem_graph_snd_inj
    ((cutoffHamiltonian g P Λ).mem_graph
      ⟨(u : GW.Fock.Carrier),freeDomain_subset_cutoffDomain g P Λ u.property⟩) hgraph rfl

end Froehlich
