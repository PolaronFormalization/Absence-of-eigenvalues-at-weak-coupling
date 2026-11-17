import Froehlich.Nodes.FC01Lifts
import Froehlich.Nodes.GW06Sectors

set_option autoImplicit false

/-! The actual bounded-momentum test core is dense in each closed high
energy space, as required for the single vector residual in PT01. -/
noncomputable section
namespace Froehlich

def highEnergyTestCore (P : GW.Space) (m : ℕ) : Submodule ℂ (HighEnergySpace P m) :=
  boundedMomentumCore.comap
    ((energyEmbedding P).comp (HighEnergySpace P m).subtypeL).toLinearMap

theorem highEnergyTestCore_dense (P : GW.Space) (m : ℕ) :
    Dense (highEnergyTestCore P m : Set (HighEnergySpace P m)) := by
  have hs : Function.Surjective (highEnergyProject P m) := by
    intro x
    refine ⟨(x : EnergySpace P),?_⟩
    apply Subtype.ext
    exact (highEnergy_mem_iff P m x).mp x.property
  have hd := hs.denseRange.comp (coreEnergyLift_denseRange P) (highEnergyProject P m).continuous
  have hd' : Dense (Set.range ((highEnergyProject P m) ∘ (coreEnergyLift P))) := hd
  apply hd'.mono
  rintro _ ⟨u,rfl⟩
  change energyEmbedding P (energyHighProjection P m (coreEnergyLift P u)) ∈ boundedMomentumCore
  rw [energyHighProjection_intertwines,coreEnergyLift_embedding]
  exact highSectorProjection_preserves_core m u

end Froehlich
