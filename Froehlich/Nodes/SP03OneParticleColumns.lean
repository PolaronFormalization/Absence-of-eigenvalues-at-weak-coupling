import Froehlich.Nodes.SP03VacuumHigh
import Froehlich.Nodes.SP03SchurForm

/-! Literal one-particle off-diagonal columns of the full singular form. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem onePhonon_vacuum_physical_orthogonal (P : GW.Space) (f : OneParticleEnergySpace P) :
    ⟪energyEmbedding P (onePhononEnergyLift P f),GW.Fock.vacuum⟫_ℂ = 0 := by
  rw [onePhononEnergyLift_physical,oneParticleInclusion_apply,lp.inner_single_left]
  rw [GW.Fock.vacuum_succ,inner_zero_right]

theorem fiberForm_onePhonon_vacuum (g : ℝ) (P : GW.Space) (f : OneParticleEnergySpace P) :
    (fiberFormData g P none).form (onePhononEnergyLift P f) (vacuumEnergyLift P) =
      isolatedFiberSourceLoad g P f := by
  rw [fiberForm_vacuum_column,onePhonon_vacuum_physical_orthogonal,
    fiberSourceLoad_onePhonon,mul_zero,zero_add]

theorem fiberForm_vacuum_onePhonon (g : ℝ) (P : GW.Space) (f : OneParticleEnergySpace P) :
    (fiberFormData g P none).form (vacuumEnergyLift P) (onePhononEnergyLift P f) =
      onePhononSourceLinear g P f := by
  rw [(fiberFormData g P none).hermitian,fiberForm_onePhonon_vacuum]
  rfl

theorem fiberForm_onePhonon_high (g : ℝ) (P : GW.Space)
    (f : OneParticleEnergySpace P) (u : HighEnergySpace P 2) :
    (fiberFormData g P none).form (onePhononEnergyLift P f) (u : EnergySpace P) =
      ⟪f,(twoSectorCoupling g P).adjoint u⟫_ℂ := by
  rw [(fiberFormData g P none).hermitian,fiberForm_high_onePhonon]
  simp only [Complex.star_def,inner_conj_symm]
  exact ((twoSectorCoupling g P).adjoint_inner_right f u).symm

end Froehlich
