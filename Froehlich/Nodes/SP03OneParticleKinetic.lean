import Froehlich.Nodes.SP03OneParticleSector
import Froehlich.Nodes.FB01KineticIdentityFull

/-! The one-particle kinetic term is the retained actual Fock momentum
multiplier restricted through the canonical one-particle isometry. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace Froehlich

def onePhononKineticNorm (P : GW.Space) (f : OneParticleEnergySpace P) : ℝ :=
  energyKineticNorm P (onePhononEnergyLift P f)

theorem energyNumberExpectation_onePhonon (P : GW.Space) (f : OneParticleEnergySpace P) :
    energyNumberExpectation P (onePhononEnergyLift P f) = ‖oneParticleEnergyEmbedding P f‖^2 := by
  unfold energyNumberExpectation
  rw [numberFormRoot_norm,energyNumberCoordinates_intertwines,onePhononEnergyLift_physical,
    oneParticleInclusion_apply]
  rw [tsum_eq_single 1]
  · simp only [lp.single_apply_self,Nat.cast_one,one_mul,LinearIsometryEquiv.norm_map]
  · intro m hm
    simp only [lp.single_apply_ne 2 1 _ hm,norm_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),mul_zero]

theorem onePhononKineticNorm_identity (P : GW.Space) (f : OneParticleEnergySpace P) :
    ‖f‖^2 = ‖oneParticleEnergyEmbedding P f‖^2 + onePhononKineticNorm P f ^ 2 := by
  have hk := energyKineticNorm_number_identity P (onePhononEnergyLift P f)
  change onePhononKineticNorm P f ^ 2 + energyNumberExpectation P (onePhononEnergyLift P f) =
    freeEnergy P (energyEmbedding P (onePhononEnergyLift P f)) at hk
  rw [energyNumberExpectation_onePhonon,onePhononEnergyLift_physical] at hk
  have hn := energyEmbedding_norm_identity P (onePhononEnergyLift P f)
  rw [onePhononEnergyLift_norm_sq,onePhononEnergyLift_physical,oneParticleInclusion_norm] at hn
  linarith

/-- The retained momentum multiplier is literally (k-P)_a on sector one. -/
theorem onePhononKineticComponent_ae (P : GW.Space) (a : Fin 3) (f : OneParticleEnergySpace P) :
    (fun K : GW.Fock.Coordinates 1 => (((K 0-P) a : ℝ) : ℂ) • oneParticleEnergyEmbedding P f (K 0)) =ᵐ[GW.Fock.sectorMeasure 1]
      physicalSector 1 (energyKineticComponent P a (onePhononEnergyLift P f) 1) := by
  have hk := energyKineticComponent_ae P a (onePhononEnergyLift P f) 1
  rw [onePhononEnergyLift_physical] at hk
  have hf := extraction_physical_representative (oneParticleInclusion (oneParticleEnergyEmbedding P f))
  rw [oneParticleExtraction_inclusion] at hf
  filter_upwards [hk,hf] with K hK hfK
  rw [← hK,hfK]
  simp only [energyKineticSymbol,totalMomentum,Fin.sum_univ_one,WithLp.ofLp_sub,Pi.sub_apply]

end Froehlich
