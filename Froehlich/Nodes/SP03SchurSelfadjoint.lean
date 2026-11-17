import Froehlich.Nodes.SP03SchurForm

/-! Hermitian representatives of the actual one-phonon Schur form. -/
noncomputable section
namespace Froehlich
variable (g e eps : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (heLower : -sectorEnergyConstant*|g|^2 ≤ e) (he : e ≤ 0)
    (heps : 0 ≤ eps) (hsmall : sectorQuadraticConstant*|g|^2 ≤ 1/8)

theorem twoSectorEnergyInverse_selfadjoint :
    (twoSectorEnergyInverse g e eps P hg heLower he heps hsmall).adjoint =
      twoSectorEnergyInverse g e eps P hg heLower he heps hsmall := by
  apply inverse_selfadjoint (twoSectorOperator g P (e+1-eps))
    (twoSectorEnergyInverse g e eps P hg heLower he heps hsmall)
    (twoSectorOperator_selfadjoint g P _)
  · apply ContinuousLinearMap.ext
    intro u
    exact twoSectorEnergyInverse_left_apply g e eps P hg heLower he heps hsmall u
  · apply ContinuousLinearMap.ext
    intro u
    exact twoSectorEnergyInverse_right_apply g e eps P hg heLower he heps hsmall u

theorem onePhononHighCorrection_selfadjoint :
    (onePhononHighCorrection g e eps P hg heLower he heps hsmall).adjoint =
      onePhononHighCorrection g e eps P hg heLower he heps hsmall := by
  simp only [onePhononHighCorrection,ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint,twoSectorEnergyInverse_selfadjoint]
  exact ContinuousLinearMap.comp_assoc _ _ _

theorem onePhononSchurOperator_selfadjoint
    (hd : 1/2 ≤ onePhononVacuumDenominator e eps P) :
    (onePhononSchurOperator g e eps P hg heLower he heps hsmall hd).adjoint =
      onePhononSchurOperator g e eps P hg heLower he heps hsmall hd := by
  simp only [onePhononSchurOperator,map_add,map_sub,map_smulₛₗ,
    ContinuousLinearMap.adjoint_one,Complex.conj_ofReal,
    onePhononHighCorrection_selfadjoint,onePhononMassOperator,onePhononSourceOperator,
    ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint]

end Froehlich
