import Froehlich.Nodes.SP01VacuumColumn

/-! Exact scalar-vacuum and nonvacuum decompositions on the original
physical carrier and its complete energy domain. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem vacuumInclusion_eq_smul (z : ℂ) :
    vacuumInclusion z = z • GW.Fock.vacuum := by
  simpa only [smul_eq_mul,mul_one,vacuumInclusion_one] using
    (vacuumInclusion.map_smul z (1 : ℂ))

/-- Typed scalar evaluation of the original canonical vacuum sector. -/
def vacuumCoefficient : GW.Fock.Carrier →L[ℂ] ℂ :=
  lp.evalCLM ℂ GW.Fock.Sector 2 0

theorem vacuumCoefficient_apply (u : GW.Fock.Carrier) :
    vacuumCoefficient u = u 0 := rfl

theorem fock_vacuum_high_decomposition (u : GW.Fock.Carrier) :
    vacuumInclusion (u 0) + highSectorProjection 1 u = u := by
  apply lp.ext
  funext n
  change lp.single 2 0 (u 0) n + highSectorProjection 1 u n = u n
  cases n with
  | zero => simp only [lp.single_apply_self,highSectorProjection_apply,
      show ¬1 ≤ (0 : ℕ) by omega,ite_false,add_zero]
  | succ n => simp only [lp.single_apply_ne 2 0 (u 0) (by omega : n+1 ≠ 0),
      highSectorProjection_apply,Nat.succ_le_succ (Nat.zero_le n),ite_true,zero_add]

theorem energy_vacuum_high_decomposition (P : GW.Space) (u : EnergySpace P) :
    (vacuumCoefficient (energyEmbedding P u)) • vacuumEnergyLift P +
      (highEnergyProject P 1 u : EnergySpace P) = u := by
  apply energyEmbedding_injective P
  rw [map_add,map_smul,vacuumEnergyLift_embedding]
  change (vacuumCoefficient (energyEmbedding P u)) • GW.Fock.vacuum +
    energyEmbedding P (energyHighProjection P 1 u) = energyEmbedding P u
  rw [energyHighProjection_intertwines,← vacuumInclusion_eq_smul,vacuumCoefficient_apply]
  exact fock_vacuum_high_decomposition (energyEmbedding P u)

theorem vacuumEnergyLift_high_coefficient (P : GW.Space) (u : HighEnergySpace P 1) :
    (energyEmbedding P (u : EnergySpace P)) 0 = 0 := by
  have hp := (highSector_mem_iff 1 (highEnergyEmbedding P 1 u)).mp
    (highEnergyEmbedding P 1 u).property
  rw [highEnergyEmbedding_apply] at hp
  have hz := congrArg (fun v : GW.Fock.Carrier => v 0) hp
  simpa only [highSectorProjection_apply,show ¬1 ≤ (0 : ℕ) by omega,ite_false] using hz.symm

end Froehlich
