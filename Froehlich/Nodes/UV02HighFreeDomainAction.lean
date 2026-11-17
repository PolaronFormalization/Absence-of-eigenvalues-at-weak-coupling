import Froehlich.Nodes.UV02FreeDomainAction
import Froehlich.Nodes.UV02HighDomainEquality

/-! The actual free action and projected cutoff field on the literal
maximal free domain in every closed high sector. -/
noncomputable section
namespace Froehlich

def highFreeDomainInput (P : GW.Space) (n : ℕ) (u : HighFreePhysicalDomain P n) :
    (freeFiberOperator P).domain := ⟨((u : HighSectorSpace n) : GW.Fock.Carrier),u.property⟩

def highFreeDomainEnergyCoordinate (P : GW.Space) (n : ℕ) (u : HighFreePhysicalDomain P n) :
    HighEnergySpace P n :=
  ⟨freeDomainEnergyCoordinate P (highFreeDomainInput P n u),by
    apply (highEnergy_mem_iff P n _).mpr
    apply energyEmbedding_injective P
    rw [energyHighProjection_intertwines,freeDomainEnergyCoordinate_physical]
    exact (highSector_mem_iff n (u : HighSectorSpace n)).mp (u : HighSectorSpace n).property⟩

theorem highFreeDomainEnergyCoordinate_physical (P : GW.Space) (n : ℕ) (u : HighFreePhysicalDomain P n) :
    highEnergyEmbedding P n (highFreeDomainEnergyCoordinate P n u)=(u : HighSectorSpace n) := by
  apply Subtype.ext
  exact freeDomainEnergyCoordinate_physical P (highFreeDomainInput P n u)

def highFreeAction (P : GW.Space) (n : ℕ) (u : HighFreePhysicalDomain P n) : HighSectorSpace n :=
  ⟨freeFiberOperator P (highFreeDomainInput P n u),freeGraph_preserves_high P n (u : HighSectorSpace n) _
    ((freeFiberOperator P).mem_graph (highFreeDomainInput P n u))⟩

@[simp] theorem highFreeAction_val (P : GW.Space) (n : ℕ) (u : HighFreePhysicalDomain P n) :
    (highFreeAction P n u : GW.Fock.Carrier)=freeFiberOperator P (highFreeDomainInput P n u) := rfl

theorem highCutoff_freeDomain_action (g : ℝ) (P : GW.Space) (n : ℕ) (Λ : GW.Operators.PositiveCutoff)
    (u : HighFreePhysicalDomain P n) :
    compressedHamiltonian g P n (some Λ)
      ⟨(u : HighSectorSpace n),highFreeDomain_subset_cutoffDomain g P n Λ u.property⟩=
      highFreeAction P n u+highSectorProject n
        (energySmearedField P (cutoffFormFactorL2 g Λ.val Λ.property)
          (highFreeDomainEnergyCoordinate P n u : EnergySpace P)) := by
  have hfree : (((u : HighSectorSpace n) : GW.Fock.Carrier),(highFreeAction P n u : GW.Fock.Carrier)) ∈
      (freeFiberOperator P).graph := (freeFiberOperator P).mem_graph (highFreeDomainInput P n u)
  obtain ⟨x,hx,hgraph⟩ := highFreeGraph_cutoffGraph g P n Λ (u : HighSectorSpace n) (highFreeAction P n u) hfree
  have hxeq : x=highFreeDomainEnergyCoordinate P n u := by
    apply highEnergyEmbedding_injective P n
    rw [hx,highFreeDomainEnergyCoordinate_physical]
  rw [hxeq] at hgraph
  have hact := (compressedHamiltonian g P n (some Λ)).mem_graph_snd_inj
    ((compressedHamiltonian g P n (some Λ)).mem_graph
      ⟨(u : HighSectorSpace n),highFreeDomain_subset_cutoffDomain g P n Λ u.property⟩) hgraph rfl
  have hf : highSectorProject n (highFreeAction P n u : GW.Fock.Carrier)=highFreeAction P n u := by
    apply Subtype.ext
    exact (highSector_mem_iff n (highFreeAction P n u)).mp (highFreeAction P n u).property
  rw [hact,map_add,hf]

end Froehlich
