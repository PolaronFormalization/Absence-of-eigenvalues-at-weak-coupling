import Froehlich.Nodes.SP03BlockSolution

/-! Exact energy block equations for the source elimination solution. -/
noncomputable section
namespace Froehlich
variable (g e eps : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (heLower : -sectorEnergyConstant*|g|^2 ≤ e) (he : e ≤ 0)
    (heps : 0 < eps) (hsmall : sectorQuadraticConstant*|g|^2 ≤ 1/8)
    (hd : 1/2 ≤ onePhononVacuumDenominator e eps P)
    (hd0 : 1/2 ≤ onePhononVacuumDenominator e 0 P)
    (hc : onePhononCorrectionConstant*|g|^2 ≤ 1/2)
    (hzero : ∀ f : OneParticleEnergySpace P,
      0 ≤ (inner ℂ f (onePhononSchurOperator g e 0 P hg heLower he (by norm_num) hsmall hd0 f)).re)

theorem onePhononEliminationSolveOne_equation (q : EnergySpace P) :
    (onePhononSchurOperator g e eps P hg heLower he heps.le hsmall hd) ((onePhononEliminationSolveOne g e eps P hg heLower he heps hsmall hd hd0 hc hzero) q) = (onePhononEliminationRhs g e eps P hg heLower he heps hsmall) q := by
  change (onePhononSchurOperator g e eps P hg heLower he heps.le hsmall hd) ((onePhononSchurInverse g e eps P hg heLower he heps hsmall hd hd0 hc hzero) ((onePhononEliminationRhs g e eps P hg heLower he heps hsmall) q)) = _
  exact congrArg (fun T : OneParticleEnergySpace P →L[ℂ] OneParticleEnergySpace P =>
    T ((onePhononEliminationRhs g e eps P hg heLower he heps hsmall) q)) (onePhononSchurInverse_right g e eps P hg heLower he heps hsmall hd hd0 hc hzero)

theorem onePhononEliminationSolveHigh_equation (q : EnergySpace P) :
    (twoSectorOperator g P (e+1-eps)) ((onePhononEliminationSolveHigh g e eps P hg heLower he heps hsmall hd hd0 hc hzero) q) + (twoSectorCoupling g P) ((onePhononEliminationSolveOne g e eps P hg heLower he heps hsmall hd hd0 hc hzero) q) =
      (HighEnergySpace P 2).subtypeL.adjoint q := by
  change (twoSectorOperator g P (e+1-eps)) ((twoSectorEnergyInverse g e eps P hg heLower he heps.le hsmall)
    ((HighEnergySpace P 2).subtypeL.adjoint q - (twoSectorCoupling g P) ((onePhononEliminationSolveOne g e eps P hg heLower he heps hsmall hd hd0 hc hzero) q))) +
      (twoSectorCoupling g P) ((onePhononEliminationSolveOne g e eps P hg heLower he heps hsmall hd hd0 hc hzero) q) = _
  rw [twoSectorEnergyInverse_right_apply]
  exact sub_add_cancel _ _

theorem onePhononEliminationSolveVacuum_equation (q : EnergySpace P) :
    -((onePhononVacuumDenominator e eps P : ℝ) : ℂ) * ((onePhononEliminationSolveVacuum g e eps P hg heLower he heps hsmall hd hd0 hc hzero) q) +
      (onePhononSourceLinear g P) ((onePhononEliminationSolveOne g e eps P hg heLower he heps hsmall hd hd0 hc hzero) q) = (vacuumEnergyInclusion P).adjoint q := by
  have hpos : 0 < onePhononVacuumDenominator e eps P := by linarith
  have hne : ((onePhononVacuumDenominator e eps P : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)
  change -((onePhononVacuumDenominator e eps P : ℝ) : ℂ) *
    ((((onePhononVacuumDenominator e eps P)⁻¹ : ℝ) : ℂ) *
      ((onePhononSourceLinear g P) ((onePhononEliminationSolveOne g e eps P hg heLower he heps hsmall hd hd0 hc hzero) q) - (vacuumEnergyInclusion P).adjoint q)) +
        (onePhononSourceLinear g P) ((onePhononEliminationSolveOne g e eps P hg heLower he heps hsmall hd hd0 hc hzero) q) = _
  rw [Complex.ofReal_inv]
  field_simp [hne]
  <;> ring

end Froehlich
