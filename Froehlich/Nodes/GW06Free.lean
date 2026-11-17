import Froehlich.Nodes.GW06Uniqueness
import Froehlich.Nodes.FB02Zero

/-! Zero coupling identifies the complete actual Hamiltonian with the
retained maximal free multiplication operator, not just their core actions. -/
noncomputable section
namespace Froehlich

theorem fiberHamiltonian_zero_coupling (P : GW.Space) : fiberHamiltonian 0 P = freeFiberOperator P := by
  apply Eq.symm
  apply fiberHamiltonian_unique 0 P (freeFiberOperator P) (freeFiberOperator_selfadjoint P)
  intro x
  obtain ⟨u,hu,hweak⟩ := (freeFiberOperator_graph_weak_iff P _ _).mp ((freeFiberOperator P).mem_graph x)
  refine ⟨u,hu,?_⟩
  intro w
  simpa only [singularInteraction_zero_coupling,ContinuousLinearMap.zero_apply,add_zero] using hweak w

end Froehlich
