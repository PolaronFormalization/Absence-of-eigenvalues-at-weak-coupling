import Froehlich.Nodes.FC01Lifts
import Froehlich.Nodes.GW06Sectors
import Mathlib.Topology.Sequences

set_option autoImplicit false

/-! Free-graph approximation by the actual bounded-momentum core while
preserving a prescribed high sector. -/
noncomputable section
open Filter
open scoped Topology
namespace Froehlich

def graphHighProjection (P : GW.Space) (m : ℕ) : OperatorGraphSpace P →L[ℂ] OperatorGraphSpace P :=
  (graphCoordinates P).symm.toLinearIsometry.toContinuousLinearMap.comp
    ((highSectorProjection m).comp (graphCoordinates P).toLinearIsometry.toContinuousLinearMap)

theorem graphHighProjection_physical (P : GW.Space) (m : ℕ) (x : OperatorGraphSpace P) :
    graphEmbedding P (graphHighProjection P m x) = highSectorProjection m (graphEmbedding P x) := by
  apply lp.ext
  funext n
  change sectorGraphEmbedding P n (highSectorProjection m (graphCoordinates P x) n) =
    highSectorProjection m (graphEmbedding P x) n
  rw [highSectorProjection_apply,highSectorProjection_apply]
  split_ifs
  · rfl
  · exact map_zero _

theorem highFreeGraph_core_approximation (P : GW.Space) (m : ℕ) (x : OperatorGraphSpace P)
    (hx : graphEmbedding P x ∈ HighSectorSpace m) :
    ∃ xs : ℕ → OperatorGraphSpace P,
      (∀ j, graphEmbedding P (xs j) ∈ boundedMomentumCore ∧
        graphEmbedding P (xs j) ∈ HighSectorSpace m) ∧ Tendsto xs atTop (𝓝 x) := by
  have hfix : graphHighProjection P m x = x := by
    apply graphEmbedding_injective P
    rw [graphHighProjection_physical]
    exact (highSector_mem_iff m _).mp hx
  have hc := mem_closure_image (graphHighProjection P m).continuous.continuousAt (freeOperatorCore_dense P x)
  rw [hfix] at hc
  let S : Set (OperatorGraphSpace P) := {y |
    graphEmbedding P y ∈ boundedMomentumCore ∧ graphEmbedding P y ∈ HighSectorSpace m}
  change ∃ xs : ℕ → OperatorGraphSpace P, (∀ j, xs j ∈ S) ∧ Tendsto xs atTop (𝓝 x)
  apply (mem_closure_iff_seq_limit (s := S) (a := x)).mp
  apply (closure_mono (t := S) ?_) hc
  rintro _ ⟨z,hz,rfl⟩
  constructor
  · rw [graphHighProjection_physical]
    exact highSectorProjection_preserves_core m ⟨graphEmbedding P z,hz⟩
  · apply (highSector_mem_iff m _).mpr
    rw [graphHighProjection_physical]
    exact congrArg (fun T : GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier => T (graphEmbedding P z))
      (highSectorProjection_idempotent m)

end Froehlich
