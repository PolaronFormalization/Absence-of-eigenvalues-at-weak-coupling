import Froehlich.Nodes.SP03OneParticleSector

/-! Actual full-domain free orthogonality and absence of vacuum/high coupling. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem highEnergy_low_coordinate (P : GW.Space) (n m : ℕ) (hm : m < n)
    (u : HighEnergySpace P n) : energyEmbedding P (u : EnergySpace P) m = 0 := by
  have hp := (highSector_mem_iff n (highEnergyEmbedding P n u)).mp
    (highEnergyEmbedding P n u).property
  have h := congrArg (fun v : GW.Fock.Carrier => v m) hp
  simpa only [highSectorProjection_apply,show ¬n ≤ m by omega,ite_false,
    highEnergyEmbedding_apply] using h.symm

theorem energySectorProjection_high_two_one (P : GW.Space) (u : HighEnergySpace P 2) :
    energySectorProjection P 1 (u : EnergySpace P) = 0 := by
  apply energyEmbedding_injective P
  rw [energySectorProjection_intertwines,map_zero,sectorProjection_apply,
    highEnergy_low_coordinate P 2 1 (by omega) u]
  exact lp.single_zero _ _

theorem oneParticleEnergyProjection_high_two (P : GW.Space) (u : HighEnergySpace P 2) :
    oneParticleEnergyProjection P (u : EnergySpace P) = 0 := by
  apply oneParticleEnergyEmbedding_injective P
  rw [oneParticleEnergyProjection_intertwines,map_zero,oneParticleExtraction_apply,
    highEnergy_low_coordinate P 2 1 (by omega) u,map_zero]

theorem fiberSourceLoad_high_two (g : ℝ) (P : GW.Space) (u : HighEnergySpace P 2) :
    fiberSourceLoad g P (u : EnergySpace P) = 0 := by
  change isolatedFiberSourceLoad g P (oneParticleEnergyProjection P u) = 0
  rw [oneParticleEnergyProjection_high_two,map_zero]

theorem onePhonon_high_energy_orthogonal (P : GW.Space)
    (f : OneParticleEnergySpace P) (u : HighEnergySpace P 2) :
    ⟪onePhononEnergyLift P f,(u : EnergySpace P)⟫_ℂ = 0 := by
  rw [← onePhononEnergyLift_sector P f,energySectorProjection_pairing,
    energySectorProjection_high_two_one,inner_zero_right]

theorem onePhonon_high_physical_orthogonal (P : GW.Space)
    (f : OneParticleEnergySpace P) (u : HighEnergySpace P 2) :
    ⟪energyEmbedding P (onePhononEnergyLift P f),energyEmbedding P (u : EnergySpace P)⟫_ℂ = 0 := by
  have hs := congrArg (energyEmbedding P) (onePhononEnergyLift_sector P f)
  rw [energySectorProjection_intertwines] at hs
  rw [← hs,sectorProjection_pairing,sectorProjection_apply,
    highEnergy_low_coordinate P 2 1 (by omega) u,lp.single_zero,inner_zero_right]

theorem freeFiberForm_onePhonon_high (P : GW.Space)
    (f : OneParticleEnergySpace P) (u : HighEnergySpace P 2) :
    freeFiberForm P (onePhononEnergyLift P f) u = 0 := by
  rw [freeFiberForm_apply,onePhonon_high_energy_orthogonal,
    onePhonon_high_physical_orthogonal,sub_self]

theorem fiberForm_high_onePhonon (g : ℝ) (P : GW.Space)
    (f : OneParticleEnergySpace P) (u : HighEnergySpace P 2) :
    (fiberFormData g P none).form (u : EnergySpace P) (onePhononEnergyLift P f) =
      ⟪u,twoSectorCoupling g P f⟫_ℂ := by
  rw [fiberFormData_singular_apply,freeFiberForm_hermitian,
    freeFiberForm_onePhonon_high,star_zero,zero_add]
  exact (twoSectorCoupling_spec g P f u).symm

end Froehlich
