import Froehlich.Nodes.SP03CrossSectors
import Froehlich.Nodes.SP01VacuumColumn

/-! No vacuum/high-two coupling on the complete original form domain. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem high_two_vacuum_physical_orthogonal (P : GW.Space) (u : HighEnergySpace P 2) :
    ⟪energyEmbedding P (u : EnergySpace P),GW.Fock.vacuum⟫_ℂ = 0 := by
  have hv := vacuumInclusion_pairing 1 (energyEmbedding P (u : EnergySpace P))
  rw [vacuumInclusion_one,highEnergy_low_coordinate P 2 0 (by omega) u] at hv
  have hz : ⟪GW.Fock.vacuum,energyEmbedding P (u : EnergySpace P)⟫_ℂ = 0 :=
    hv.trans (inner_zero_right _)
  rw [← inner_conj_symm,hz,map_zero]

theorem fiberForm_high_two_vacuum (g : ℝ) (P : GW.Space) (u : HighEnergySpace P 2) :
    (fiberFormData g P none).form (u : EnergySpace P) (vacuumEnergyLift P) = 0 := by
  rw [fiberForm_vacuum_column,high_two_vacuum_physical_orthogonal,
    fiberSourceLoad_high_two,mul_zero,zero_add]

theorem fiberForm_vacuum_high_two (g : ℝ) (P : GW.Space) (u : HighEnergySpace P 2) :
    (fiberFormData g P none).form (vacuumEnergyLift P) (u : EnergySpace P) = 0 := by
  rw [(fiberFormData g P none).hermitian,fiberForm_high_two_vacuum,star_zero]

end Froehlich
