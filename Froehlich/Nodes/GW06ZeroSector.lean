import Froehlich.Nodes.GW06CompressionAction

/-! The zero-sector complement is the full canonical physical space,
including equality of the complete operator graphs under its inclusion. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem energyHighProjection_zero_apply (P : GW.Space) (x : EnergySpace P) :
    energyHighProjection P 0 x = x := by
  apply energyEmbedding_injective P
  rw [energyHighProjection_intertwines]
  rfl

def highEnergyZeroLift (P : GW.Space) (x : EnergySpace P) : HighEnergySpace P 0 :=
  ⟨x,(highEnergy_mem_iff P 0 x).mpr (energyHighProjection_zero_apply P x)⟩

def highSectorZeroLift (u : GW.Fock.Carrier) : HighSectorSpace 0 :=
  ⟨u,(highSector_mem_iff 0 u).mpr rfl⟩

theorem compressed_zero_graph_iff (g : ℝ) (P : GW.Space) (i : Option GW.Operators.PositiveCutoff)
    (u f : HighSectorSpace 0) :
    (u,f) ∈ (compressedHamiltonian g P 0 i).graph ↔
      ((u : GW.Fock.Carrier),(f : GW.Fock.Carrier)) ∈ (GW.Operators.formOperator (fiberFormData g P i)).graph := by
  constructor
  · intro hh
    obtain ⟨x,hx,h⟩ := (compressedHamiltonian_graph_iff g P 0 i u f).mp hh
    have ht : ∀ w : EnergySpace P, (fiberFormData g P i).form w (x : EnergySpace P) =
        ⟪energyEmbedding P w,(f : GW.Fock.Carrier)⟫_ℂ := by
      intro w
      exact h (highEnergyZeroLift P w)
    obtain ⟨hm,hv⟩ := GW.Operators.formOperator_domain_of_equation
      (fiberFormData g P i) (x : EnergySpace P) (f : GW.Fock.Carrier) ht
    exact (GW.Operators.formOperator (fiberFormData g P i)).mem_graph_iff.mpr
      ⟨⟨energyEmbedding P x,hm⟩,congrArg (fun z : HighSectorSpace 0 => (z : GW.Fock.Carrier)) hx,hv⟩
  · intro hh
    obtain ⟨v,hv⟩ := (GW.Operators.formOperator (fiberFormData g P i)).mem_graph_iff'.mp hh
    let x := GW.Operators.operatorFormCoordinate (fiberFormData g P i) v
    apply (compressedHamiltonian_graph_iff g P 0 i u f).mpr
    refine ⟨highEnergyZeroLift P x, ?_, ?_⟩
    · apply Subtype.ext
      exact (GW.Operators.operatorFormCoordinate_embedding (fiberFormData g P i) v).trans (congrArg Prod.fst hv)
    · intro w
      have ht := GW.Operators.formOperator_form_identity (fiberFormData g P i) v (w : EnergySpace P)
      exact ht.trans (congrArg (fun z : GW.Fock.Carrier => ⟪energyEmbedding P w,z⟫_ℂ) (congrArg Prod.snd hv))

end Froehlich
