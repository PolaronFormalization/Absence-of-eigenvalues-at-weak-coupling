import Froehlich.Nodes.FC01Polynomials
import Froehlich.Nodes.FC01EnergyDensity
import Froehlich.Nodes.FC01Selections

noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal Topology
namespace Froehlich

def coreEnergyLift (P : GW.Space) : boundedMomentumCore →ₗ[ℂ] EnergySpace P :=
  (energyWeightedGraph P).product.comp
    (Submodule.inclusion (core_mem_energyWeightOperator_domain P))

theorem coreEnergyLift_embedding (P : GW.Space) (u : boundedMomentumCore) :
    energyEmbedding P (coreEnergyLift P u) = (u : GW.Fock.Carrier) :=
  (energyWeightedGraph P).embedding_product _

theorem coreEnergyLift_range (P : GW.Space) : Set.range (coreEnergyLift P) =
    {x : EnergySpace P | energyEmbedding P x ∈ boundedMomentumCore} := by
  ext x
  constructor
  · rintro ⟨u,rfl⟩
    simpa only [Set.mem_setOf_eq, coreEnergyLift_embedding] using u.property
  · intro hx
    refine ⟨⟨energyEmbedding P x,hx⟩,?_⟩
    apply energyEmbedding_injective P
    exact coreEnergyLift_embedding P _

theorem coreEnergyLift_denseRange (P : GW.Space) : DenseRange (coreEnergyLift P) := by
  change Dense (Set.range (coreEnergyLift P))
  rw [coreEnergyLift_range]
  exact energyCore_dense P

def coreFreeGraphLift (P : GW.Space) : boundedMomentumCore →ₗ[ℂ] OperatorGraphSpace P :=
  (graphCoordinates P).symm.toLinearMap.comp
    ((graphWeightOperator P).toFun.comp
      (Submodule.inclusion (core_mem_freeFiberOperator_domain P)))

theorem coreFreeGraphLift_embedding (P : GW.Space) (u : boundedMomentumCore) :
    graphEmbedding P (coreFreeGraphLift P u) = (u : GW.Fock.Carrier) :=
  graphEmbedding_product P _

theorem coreFreeGraphLift_range (P : GW.Space) : Set.range (coreFreeGraphLift P) =
    {x : OperatorGraphSpace P | graphEmbedding P x ∈ boundedMomentumCore} := by
  ext x
  constructor
  · rintro ⟨u,rfl⟩
    simpa only [Set.mem_setOf_eq, coreFreeGraphLift_embedding] using u.property
  · intro hx
    refine ⟨⟨graphEmbedding P x,hx⟩,?_⟩
    apply graphEmbedding_injective P
    exact coreFreeGraphLift_embedding P _

theorem coreFreeGraphLift_denseRange (P : GW.Space) : DenseRange (coreFreeGraphLift P) := by
  change Dense (Set.range (coreFreeGraphLift P))
  rw [coreFreeGraphLift_range]
  exact freeOperatorCore_dense P

end Froehlich
