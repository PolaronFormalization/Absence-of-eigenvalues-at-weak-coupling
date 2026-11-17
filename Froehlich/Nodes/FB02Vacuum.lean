import Froehlich.Nodes.FB02A
import Froehlich.Nodes.FC01Selections
import Froehlich.Nodes.LD01

/-! The scalar vacuum in the form domain and the actual finite-cutoff
vacuum column. No singular-Hamiltonian operator-domain assertion is made. -/
noncomputable section
open scoped InnerProductSpace ENNReal
namespace Froehlich

def vacuumCore : boundedMomentumCore := ⟨GW.Fock.vacuum,vacuum_mem_boundedMomentumCore⟩
def vacuumEnergyLift (P : GW.Space) : EnergySpace P := coreEnergyLift P vacuumCore

theorem vacuumEnergyLift_embedding (P : GW.Space) :
    energyEmbedding P (vacuumEnergyLift P) = GW.Fock.vacuum := coreEnergyLift_embedding P vacuumCore

theorem coreNumberLift_vacuum : coreNumberLift vacuumCore = numberVacuumLift := by
  apply numberFormEmbedding_injective
  rw [coreNumberLift_embedding,numberFormEmbedding_vacuum]
  rfl

theorem sectorCreation_vacuum (f : GW.OnePhonon) :
    GW.Fock.sectorCreation GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel f) 0 (1 : ℂ) =
      oneParticleCoordinate f := by
  have h := congrArg (fun z : GW.Fock.kernelFixed (E := ℂ) 1 =>
    (GW.Fock.ordinarySectorKernel 1).symm z)
      (GW.Fock.kernelCreation_vacuum (GW.Fock.ordinaryKernel f) (1 : ℂ))
  change GW.Fock.sectorCreation GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel f) 0 (1 : ℂ) =
    oneParticleCoordinate ((GW.Fock.ordinaryKernel f) 1) at h
  simpa only [GW.Fock.ordinaryKernel,ContinuousLinearMap.toSpanSingleton_apply_one] using h

theorem creationRestriction_vacuum (f : GW.OnePhonon) :
    creationRestriction f (coreNumberLift vacuumCore) = oneParticleInclusion f := by
  apply lp.ext
  funext n
  rw [oneParticleInclusion_apply]
  cases n with
  | zero =>
    rw [creationRestriction_apply,GW.Fock.ordinaryCreation_zero]
    simp only [lp.single_apply_ne _ _ _ (by decide : (0 : ℕ) ≠ 1)]
  | succ n =>
    rw [creationRestriction_core_succ]
    change GW.Fock.sectorCreation GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel f) n
      (GW.Fock.vacuum n) = _
    cases n with
    | zero =>
      rw [GW.Fock.vacuum_zero,lp.single_apply_self]
      exact sectorCreation_vacuum f
    | succ n =>
      rw [GW.Fock.vacuum_succ,map_zero]
      simp only [lp.single_apply_ne _ _ _ (by omega : n+1+1 ≠ 1)]

theorem annihilationRestriction_vacuum (f : GW.OnePhonon) :
    annihilationRestriction f (coreNumberLift vacuumCore) = 0 := by
  rw [annihilationRestriction_eq_contraction,coreNumberLift_vacuum,annihilationField_vacuum,map_zero]

theorem fieldRestriction_vacuum (f : GW.OnePhonon) :
    fieldRestriction f (coreNumberLift vacuumCore) = oneParticleInclusion f := by
  change annihilationRestriction f (coreNumberLift vacuumCore) +
    creationRestriction f (coreNumberLift vacuumCore) = _
  rw [annihilationRestriction_vacuum,creationRestriction_vacuum,zero_add]

end Froehlich
