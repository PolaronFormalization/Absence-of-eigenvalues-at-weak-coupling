import Froehlich.Nodes.UV01Coupling
import Froehlich.Nodes.KA01TwoParticle
import Froehlich.Nodes.FB02SectorSelection

/-! Actual cutoff one-to-high coupling: the annihilation vacuum component
is removed by the genuine high-two projection, leaving KA01's creation vector. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem highTwo_field_oneParticle (v f : GW.OnePhonon) :
    highSectorProjection 2 (fieldRestriction v (numberOneParticleLift f)) =
      (oneToHighMap v f : GW.Fock.Carrier) := by
  apply lp.ext
  funext n
  rw [highSectorProjection_apply]
  by_cases hn : 2 ≤ n
  · rw [if_pos hn]
    change annihilationRestriction v (numberOneParticleLift f) n +
      creationRestriction v (numberOneParticleLift f) n = _
    rw [←oneToHighMap_eq_creation,annihilationRestriction_sector,
      numberFormEmbedding_oneParticleLift,oneParticleInclusion_apply,
      lp.single_apply_ne _ _ _ (show n+1 ≠ 1 by omega),map_zero,zero_add]
  · rw [if_neg hn,oneToHighMap_physical,
      lp.single_apply_ne _ _ _ (show n ≠ 2 by omega)]

theorem onePhononEnergyLift_number (P : GW.Space) (f : OneParticleEnergySpace P) :
    energyNumberCoordinates P (onePhononEnergyLift P f) =
      numberOneParticleLift (oneParticleEnergyEmbedding P f) := by
  apply numberFormEmbedding_injective
  rw [energyNumberCoordinates_intertwines,onePhononEnergyLift_physical,
    numberFormEmbedding_oneParticleLift]

theorem cutoffTwoSectorCouplingLoad_physical (g : ℝ) (P : GW.Space)
    (Λ : GW.Operators.PositiveCutoff) (f : OneParticleEnergySpace P) (w : HighEnergySpace P 2) :
    cutoffTwoSectorCouplingLoad g P Λ f w =
      ⟪highEnergyEmbedding P 2 w,
        oneToHighMap (cutoffFormFactorL2 g Λ.val Λ.property) (oneParticleEnergyEmbedding P f)⟫_ℂ := by
  rw [cutoffTwoSectorCouplingLoad_apply,cutoffInteractionForm_apply,
    ←fieldRestriction_eq_ordinaryField,onePhononEnergyLift_number]
  have hp := highSectorProjection_pairing 2
    (energyEmbedding P (w : EnergySpace P))
    (fieldRestriction (cutoffFormFactorL2 g Λ.val Λ.property)
      (numberOneParticleLift (oneParticleEnergyEmbedding P f)))
  have hw := (highSector_mem_iff 2 _).mp (highEnergyEmbedding P 2 w).property
  change highSectorProjection 2 (energyEmbedding P (w : EnergySpace P)) =
    energyEmbedding P (w : EnergySpace P) at hw
  rw [hw,highTwo_field_oneParticle] at hp
  exact hp

theorem cutoffTwoSectorCoupling_physicalLoad (g : ℝ) (P : GW.Space)
    (Λ : GW.Operators.PositiveCutoff) (f : OneParticleEnergySpace P) :
    cutoffTwoSectorCoupling g P Λ f = (highEnergyEmbedding P 2).adjoint
      (oneToHighMap (cutoffFormFactorL2 g Λ.val Λ.property) (oneParticleEnergyEmbedding P f)) := by
  rw [cutoffTwoSectorCoupling_eq_loadRiesz]
  apply Eq.symm
  apply loadRiesz_unique
  intro w
  rw [cutoffTwoSectorCouplingLoad_physical]
  exact ((highEnergyEmbedding P 2).adjoint_inner_right w
    (oneToHighMap (cutoffFormFactorL2 g Λ.val Λ.property) (oneParticleEnergyEmbedding P f))).symm

end Froehlich
