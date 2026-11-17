import Froehlich.Nodes.SP03InverseOrder
import Froehlich.Nodes.FB02
import Froehlich.Nodes.EN02OneParticle

/-! SP03's actual off-diagonal source, in the isolated one-particle
energy norm. Its Riesz vector represents the conjugate-dual load. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

def onePhononEnergyLift (P : GW.Space) : OneParticleEnergySpace P →L[ℂ] EnergySpace P :=
  (oneParticleInheritedFockLift P).comp (isolatedToInherited P)

theorem onePhononEnergyLift_physical (P : GW.Space) (f : OneParticleEnergySpace P) :
    energyEmbedding P (onePhononEnergyLift P f) = oneParticleInclusion (oneParticleEnergyEmbedding P f) := by
  simp only [onePhononEnergyLift,ContinuousLinearMap.comp_apply,
    oneParticleInheritedFockLift_intertwines,isolatedToInherited_intertwines]

theorem onePhononEnergyLift_norm_le (P : GW.Space) (f : OneParticleEnergySpace P) :
    ‖onePhononEnergyLift P f‖ ≤ Real.sqrt 2 * ‖f‖ := by
  change ‖oneParticleInheritedFockLift P (isolatedToInherited P f)‖ ≤ _
  rw [oneParticleInheritedFockLift_norm]
  exact ((isolatedToInherited P).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right (isolatedToInherited_norm P) (norm_nonneg f))

def twoSectorCouplingLoad (g : ℝ) (P : GW.Space) (f : OneParticleEnergySpace P) :
    ConjugateLoad (HighEnergySpace P 2) :=
  ((singularInteraction g P).flip (onePhononEnergyLift P f)).comp (HighEnergySpace P 2).subtypeL

theorem twoSectorCouplingLoad_apply (g : ℝ) (P : GW.Space)
    (f : OneParticleEnergySpace P) (w : HighEnergySpace P 2) :
    twoSectorCouplingLoad g P f w = singularInteraction g P w (onePhononEnergyLift P f) := rfl

def twoSectorCoupling (g : ℝ) (P : GW.Space) :
    OneParticleEnergySpace P →L[ℂ] HighEnergySpace P 2 :=
  (HighEnergySpace P 2).subtypeL.adjoint.comp
    ((formRepresentative (singularInteraction g P)).comp (onePhononEnergyLift P))

theorem twoSectorCoupling_spec (g : ℝ) (P : GW.Space)
    (f : OneParticleEnergySpace P) (w : HighEnergySpace P 2) :
    ⟪w,twoSectorCoupling g P f⟫_ℂ = twoSectorCouplingLoad g P f w := by
  rw [twoSectorCoupling,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,
    (HighEnergySpace P 2).subtypeL.adjoint_inner_right]
  exact (formRepresentative_spec (singularInteraction g P) w (onePhononEnergyLift P f)).symm

theorem twoSectorCoupling_eq_loadRiesz (g : ℝ) (P : GW.Space) (f : OneParticleEnergySpace P) :
    twoSectorCoupling g P f = loadRiesz (twoSectorCouplingLoad g P f) := by
  apply loadRiesz_unique
  intro w
  exact (twoSectorCoupling_spec g P f w).symm

theorem twoSectorCouplingLoad_norm_le (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1)
    (f : OneParticleEnergySpace P) :
    ‖twoSectorCouplingLoad g P f‖ ≤ Real.sqrt 2 * phiMixedConstant * |g| * ‖f‖ := by
  have hc := phiMixedConstant_pos
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  rw [twoSectorCouplingLoad_apply]
  have h := fb02_smallCoupling_mixed g P (w : EnergySpace P) (onePhononEnergyLift P f) hg
  calc
    _ ≤ phiMixedConstant * |g| * ‖w‖ * ‖onePhononEnergyLift P f‖ := h
    _ ≤ phiMixedConstant * |g| * ‖w‖ * (Real.sqrt 2 * ‖f‖) :=
      mul_le_mul_of_nonneg_left (onePhononEnergyLift_norm_le P f) (by positivity)
    _ = _ := by ring

theorem twoSectorCoupling_norm_le (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1) :
    ‖twoSectorCoupling g P‖ ≤ Real.sqrt 2 * phiMixedConstant * |g| := by
  have hc := phiMixedConstant_pos
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  rw [twoSectorCoupling_eq_loadRiesz,loadRiesz_norm]
  exact twoSectorCouplingLoad_norm_le g P hg f

end Froehlich
