import Froehlich.Nodes.SP01VacuumDecomposition
import Froehlich.Nodes.FA04

/-! The actual bounded direct-sum energy coordinates for vacuum Schur
elimination. The scalar coordinate retains its usual complex norm. -/
noncomputable section
namespace Froehlich

def vacuumEnergyJoin (P : GW.Space) : (ℂ × HighEnergySpace P 1) →L[ℂ] EnergySpace P :=
  (ContinuousLinearMap.toSpanSingleton ℂ (vacuumEnergyLift P)).comp (.fst ℂ ℂ (HighEnergySpace P 1)) +
    (HighEnergySpace P 1).subtypeL.comp (.snd ℂ ℂ (HighEnergySpace P 1))

def vacuumEnergySplit (P : GW.Space) : EnergySpace P →L[ℂ] (ℂ × HighEnergySpace P 1) :=
  (vacuumCoefficient.comp (energyEmbedding P)).prod (highEnergyProject P 1)

theorem vacuumEnergyJoin_apply (P : GW.Space) (z : ℂ × HighEnergySpace P 1) :
    vacuumEnergyJoin P z = z.1 • vacuumEnergyLift P + (z.2 : EnergySpace P) := rfl

theorem vacuumEnergySplit_apply (P : GW.Space) (u : EnergySpace P) :
    vacuumEnergySplit P u = (vacuumCoefficient (energyEmbedding P u),highEnergyProject P 1 u) := rfl

theorem vacuumEnergyJoin_split (P : GW.Space) (u : EnergySpace P) :
    vacuumEnergyJoin P (vacuumEnergySplit P u) = u :=
  energy_vacuum_high_decomposition P u

theorem vacuumCoefficient_vacuumEnergyLift (P : GW.Space) :
    vacuumCoefficient (energyEmbedding P (vacuumEnergyLift P)) = 1 := by
  rw [vacuumEnergyLift_embedding,vacuumCoefficient_apply,GW.Fock.vacuum_zero]

theorem vacuumCoefficient_highEnergy (P : GW.Space) (u : HighEnergySpace P 1) :
    vacuumCoefficient (energyEmbedding P (u : EnergySpace P)) = 0 := by
  rw [vacuumCoefficient_apply]
  exact vacuumEnergyLift_high_coefficient P u

theorem vacuumEnergyJoin_injective (P : GW.Space) : Function.Injective (vacuumEnergyJoin P) := by
  intro x y h
  have hc := congrArg (fun u => vacuumCoefficient (energyEmbedding P u)) h
  simp only [vacuumEnergyJoin_apply,map_add,map_smul,vacuumCoefficient_vacuumEnergyLift,
    vacuumCoefficient_highEnergy,smul_eq_mul,mul_one,add_zero] at hc
  apply Prod.ext hc
  apply Subtype.ext
  have hh := h
  rw [vacuumEnergyJoin_apply,vacuumEnergyJoin_apply,hc] at hh
  exact add_left_cancel hh

theorem vacuumEnergySplit_join (P : GW.Space) (z : ℂ × HighEnergySpace P 1) :
    vacuumEnergySplit P (vacuumEnergyJoin P z) = z := by
  apply vacuumEnergyJoin_injective P
  exact vacuumEnergyJoin_split P (vacuumEnergyJoin P z)

end Froehlich
