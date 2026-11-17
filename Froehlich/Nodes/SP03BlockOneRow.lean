import Froehlich.Nodes.SP03BlockRows

/-! The remaining exact mixed one-particle block equation. -/
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

theorem onePhononEliminationSolveOne_full_equation (q : EnergySpace P) :
    (onePhononEliminationSolveOne g e eps P hg heLower he heps hsmall hd hd0 hc hzero) q + ((eps-e-1 : ℝ) : ℂ) •
      (onePhononMassOperator P) ((onePhononEliminationSolveOne g e eps P hg heLower he heps hsmall hd hd0 hc hzero) q) +
      (onePhononSourceLinear g P).adjoint ((onePhononEliminationSolveVacuum g e eps P hg heLower he heps hsmall hd hd0 hc hzero) q) +
      (twoSectorCoupling g P).adjoint ((onePhononEliminationSolveHigh g e eps P hg heLower he heps hsmall hd hd0 hc hzero) q) = (onePhononEnergyLift P).adjoint q := by
  have hs := onePhononEliminationSolveOne_equation g e eps P hg heLower he heps hsmall hd hd0 hc hzero q
  simp only [onePhononSchurOperator,onePhononHighCorrection,onePhononSourceOperator,
    onePhononEliminationRhs,ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply] at hs
  simp only [onePhononEliminationSolveVacuum,onePhononEliminationSolveHigh,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.sub_apply,
    map_sub,map_smul]
  linear_combination (norm := module) hs

end Froehlich
