import Froehlich.Nodes.SP03SchurInverse
import Froehlich.Nodes.SP03VacuumHigh
import Froehlich.Nodes.SP01EnergyResolvent

/-! Literal bounded energy solution maps for the source three-block elimination.
These definitions use only actual energy embeddings and dual adjoints. -/
noncomputable section
namespace Froehlich

def vacuumEnergyInclusion (P : GW.Space) : ℂ →L[ℂ] EnergySpace P :=
  (ContinuousLinearMap.id ℂ ℂ).smulRight (vacuumEnergyLift P)

variable (g e eps : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (heLower : -sectorEnergyConstant*|g|^2 ≤ e) (he : e ≤ 0)
    (heps : 0 < eps) (hsmall : sectorQuadraticConstant*|g|^2 ≤ 1/8)
    (hd : 1/2 ≤ onePhononVacuumDenominator e eps P)
    (hd0 : 1/2 ≤ onePhononVacuumDenominator e 0 P)
    (hc : onePhononCorrectionConstant*|g|^2 ≤ 1/2)
    (hzero : ∀ f : OneParticleEnergySpace P,
      0 ≤ (inner ℂ f (onePhononSchurOperator g e 0 P hg heLower he (by norm_num) hsmall hd0 f)).re)

def onePhononEliminationRhs : EnergySpace P →L[ℂ] OneParticleEnergySpace P :=
  (onePhononEnergyLift P).adjoint +
    (((onePhononVacuumDenominator e eps P)⁻¹ : ℝ) : ℂ) • ((onePhononSourceLinear g P).adjoint.comp (vacuumEnergyInclusion P).adjoint) -
    (twoSectorCoupling g P).adjoint.comp
      ((twoSectorEnergyInverse g e eps P hg heLower he heps.le hsmall).comp (HighEnergySpace P 2).subtypeL.adjoint)

def onePhononEliminationSolveOne : EnergySpace P →L[ℂ] OneParticleEnergySpace P :=
  (onePhononSchurInverse g e eps P hg heLower he heps hsmall hd hd0 hc hzero).comp
    (onePhononEliminationRhs g e eps P hg heLower he heps hsmall)

def onePhononEliminationSolveVacuum : EnergySpace P →L[ℂ] ℂ :=
  (((onePhononVacuumDenominator e eps P)⁻¹ : ℝ) : ℂ) •
    ((onePhononSourceLinear g P).comp (onePhononEliminationSolveOne g e eps P hg heLower he heps hsmall hd hd0 hc hzero) - (vacuumEnergyInclusion P).adjoint)

def onePhononEliminationSolveHigh : EnergySpace P →L[ℂ] HighEnergySpace P 2 :=
  (twoSectorEnergyInverse g e eps P hg heLower he heps.le hsmall).comp
    ((HighEnergySpace P 2).subtypeL.adjoint - (twoSectorCoupling g P).comp
      (onePhononEliminationSolveOne g e eps P hg heLower he heps hsmall hd hd0 hc hzero))

def onePhononFullEnergyInverse : EnergySpace P →L[ℂ] EnergySpace P :=
  (vacuumEnergyInclusion P).comp (onePhononEliminationSolveVacuum g e eps P hg heLower he heps hsmall hd hd0 hc hzero) +
    (onePhononEnergyLift P).comp (onePhononEliminationSolveOne g e eps P hg heLower he heps hsmall hd hd0 hc hzero) +
      (HighEnergySpace P 2).subtypeL.comp (onePhononEliminationSolveHigh g e eps P hg heLower he heps hsmall hd hd0 hc hzero)

end Froehlich
