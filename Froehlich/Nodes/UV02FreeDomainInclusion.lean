import Froehlich.Nodes.GW06
import Froehlich.Nodes.FD02FreeForm

/-! The forward cutoff-domain inclusion follows from the actual free
maximal graph and the full energy weak equation, not from core equality. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem freeGraph_cutoffGraph (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff)
    (u f : GW.Fock.Carrier) (hfree : (u,f) ∈ (freeFiberOperator P).graph) :
    ∃ x : EnergySpace P, energyEmbedding P x=u ∧
      (u,f+energySmearedField P (cutoffFormFactorL2 g Λ.val Λ.property) x) ∈ (cutoffHamiltonian g P Λ).graph := by
  obtain ⟨x,hx,hweak⟩ := (freeFiberOperator_graph_weak_iff P u f).mp hfree
  have hcut : ∀ w : EnergySpace P, (fiberFormData g P (some Λ)).form w x =
      ⟪energyEmbedding P w,f+energySmearedField P (cutoffFormFactorL2 g Λ.val Λ.property) x⟫_ℂ := by
    intro w
    rw [fiberFormData_cutoff_apply,hweak w,inner_add_right]
    change ⟪energyEmbedding P w,f⟫_ℂ+
      ⟪energyEmbedding P w,energySmearedField P (cutoffFormFactorL2 g Λ.val Λ.property) x⟫_ℂ = _
    rfl
  have hd := GW.Operators.formOperator_domain_of_equation (fiberFormData g P (some Λ)) x
    (f+energySmearedField P (cutoffFormFactorL2 g Λ.val Λ.property) x) hcut
  refine ⟨x,hx,?_⟩
  rw [←hx]
  exact (cutoffHamiltonian g P Λ).mem_graph_iff.mpr
    ⟨⟨energyEmbedding P x,hd.choose⟩,rfl,hd.choose_spec⟩

theorem freeDomain_subset_cutoffDomain (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff) :
    (freeFiberOperator P).domain ≤ (cutoffHamiltonian g P Λ).domain := by
  intro u hu
  obtain ⟨x,hx,hgraph⟩ := freeGraph_cutoffGraph g P Λ u
    (freeFiberOperator P ⟨u,hu⟩) ((freeFiberOperator P).mem_graph ⟨u,hu⟩)
  exact (cutoffHamiltonian g P Λ).mem_domain_of_mem_graph hgraph

end Froehlich
