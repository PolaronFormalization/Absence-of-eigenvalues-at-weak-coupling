import Froehlich.Nodes.SP01ScalarIdentities
import Froehlich.Nodes.SP01VacuumColumn

/-! Scalar vacuum normalization and vanishing singular source on the vacuum.
Only the vacuum's form-domain lift is used. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem oneParticleEnergyProjection_vacuum (P : GW.Space) :
    oneParticleEnergyProjection P (vacuumEnergyLift P) = 0 := by
  apply oneParticleEnergyEmbedding_injective P
  rw [oneParticleEnergyProjection_intertwines,vacuumEnergyLift_embedding,map_zero,
    oneParticleExtraction_apply,GW.Fock.vacuum_succ,map_zero]

theorem fiberSourceLoad_vacuum (g : ℝ) (P : GW.Space) :
    fiberSourceLoad g P (vacuumEnergyLift P) = 0 := by
  change isolatedFiberSourceLoad g P (oneParticleEnergyProjection P (vacuumEnergyLift P)) = 0
  rw [oneParticleEnergyProjection_vacuum,map_zero]

theorem vacuum_inner_self : ⟪GW.Fock.vacuum,GW.Fock.vacuum⟫_ℂ = 1 := by
  rw [inner_self_eq_norm_sq_to_K,GW.Fock.vacuum_norm]
  norm_num

theorem fiberForm_vacuum_diagonal (g : ℝ) (P : GW.Space) :
    (fiberFormData g P none).form (vacuumEnergyLift P) (vacuumEnergyLift P) = (‖P‖^2 : ℂ) := by
  rw [fiberForm_vacuum_column,vacuumEnergyLift_embedding,vacuum_inner_self,
    fiberSourceLoad_vacuum,mul_one,add_zero]

end Froehlich
