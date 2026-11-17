import Froehlich.Nodes.SP03OneParticleNorm
import Froehlich.Nodes.SP01VacuumDecomposition

/-! The literal one-particle form column and full vacuum/one/high
energy decomposition used by the source Schur elimination. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem onePhononEnergyLift_sector (P : GW.Space) (f : OneParticleEnergySpace P) :
    energySectorProjection P 1 (onePhononEnergyLift P f) = onePhononEnergyLift P f := by
  apply energyEmbedding_injective P
  rw [energySectorProjection_intertwines,onePhononEnergyLift_physical,
    ← oneParticleInclusion_extraction,oneParticleExtraction_inclusion]

theorem singularInteraction_onePhonon (g : ℝ) (P : GW.Space) (f h : OneParticleEnergySpace P) :
    singularInteraction g P (onePhononEnergyLift P f) (onePhononEnergyLift P h) = 0 := by
  have hs := fb02_singular_selection g P 1 1 (onePhononEnergyLift P f)
    (onePhononEnergyLift P h) (by omega) (by omega)
  simpa only [onePhononEnergyLift_sector] using hs

theorem fiberForm_onePhonon (g : ℝ) (P : GW.Space) (f h : OneParticleEnergySpace P) :
    (fiberFormData g P none).form (onePhononEnergyLift P f) (onePhononEnergyLift P h) = ⟪f,h⟫_ℂ := by
  rw [fiberFormData_singular_apply,freeFiberForm_onePhonon,singularInteraction_onePhonon,add_zero]

theorem oneParticleEnergyProjection_lift (P : GW.Space) (f : OneParticleEnergySpace P) :
    oneParticleEnergyProjection P (onePhononEnergyLift P f) = f := by
  apply oneParticleEnergyEmbedding_injective P
  rw [oneParticleEnergyProjection_intertwines,onePhononEnergyLift_physical,oneParticleExtraction_inclusion]

theorem fiberSourceLoad_onePhonon (g : ℝ) (P : GW.Space) (f : OneParticleEnergySpace P) :
    fiberSourceLoad g P (onePhononEnergyLift P f) = isolatedFiberSourceLoad g P f := by
  change isolatedFiberSourceLoad g P (oneParticleEnergyProjection P (onePhononEnergyLift P f)) = _
  rw [oneParticleEnergyProjection_lift]

theorem fock_vacuum_one_high_decomposition (u : GW.Fock.Carrier) :
    vacuumInclusion (u 0) + oneParticleInclusion (oneParticleExtraction u) + highSectorProjection 2 u = u := by
  rw [oneParticleInclusion_extraction]
  apply lp.ext
  funext n
  change lp.single 2 0 (u 0) n + lp.single 2 1 (u 1) n + highSectorProjection 2 u n = u n
  cases n with
  | zero => simp only [lp.single_apply_self,lp.single_apply_ne 2 1 (u 1) (by omega : 0 ≠ 1),
      highSectorProjection_apply,show ¬2 ≤ (0 : ℕ) by omega,ite_false,add_zero]
  | succ n =>
    cases n with
    | zero => simp only [lp.single_apply_self,lp.single_apply_ne 2 0 (u 0) (by omega : 1 ≠ 0),
        highSectorProjection_apply,show ¬2 ≤ (1 : ℕ) by omega,ite_false,zero_add,add_zero]
    | succ n => simp only [lp.single_apply_ne 2 0 (u 0) (by omega : n+1+1 ≠ 0),
        lp.single_apply_ne 2 1 (u 1) (by omega : n+1+1 ≠ 1),highSectorProjection_apply,
        show 2 ≤ n+1+1 by omega,ite_true,zero_add]

theorem energy_vacuum_one_high_decomposition (P : GW.Space) (u : EnergySpace P) :
    vacuumCoefficient (energyEmbedding P u) • vacuumEnergyLift P +
      onePhononEnergyLift P (oneParticleEnergyProjection P u) +
      (highEnergyProject P 2 u : EnergySpace P) = u := by
  apply energyEmbedding_injective P
  rw [map_add,map_add,map_smul,vacuumEnergyLift_embedding,onePhononEnergyLift_physical,
    oneParticleEnergyProjection_intertwines]
  change vacuumCoefficient (energyEmbedding P u) • GW.Fock.vacuum +
    oneParticleInclusion (oneParticleExtraction (energyEmbedding P u)) +
    energyEmbedding P (energyHighProjection P 2 u) = energyEmbedding P u
  rw [energyHighProjection_intertwines,← vacuumInclusion_eq_smul,vacuumCoefficient_apply]
  exact fock_vacuum_one_high_decomposition (energyEmbedding P u)

end Froehlich
