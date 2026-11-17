import Froehlich.Nodes.SP03SchurCoercivity

/-! The genuine two-sided bounded energy inverse used in block elimination. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich
variable (g e eps : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (heLower : -sectorEnergyConstant*|g|^2 ≤ e) (he : e ≤ 0)
    (heps : 0 < eps) (hsmall : sectorQuadraticConstant*|g|^2 ≤ 1/8)
    (hd : 1/2 ≤ onePhononVacuumDenominator e eps P)
    (hd0 : 1/2 ≤ onePhononVacuumDenominator e 0 P)
    (hc : onePhononCorrectionConstant*|g|^2 ≤ 1/2)
    (hzero : ∀ f : OneParticleEnergySpace P,
      0 ≤ (⟪f,onePhononSchurOperator g e 0 P hg heLower he (by norm_num) hsmall hd0 f⟫_ℂ).re)

def onePhononSchurInverse : OneParticleEnergySpace P →L[ℂ] OneParticleEnergySpace P :=
  coerciveEnergyInverse (onePhononSchurOperator g e eps P hg heLower he heps.le hsmall hd) (onePhononSchurOperator_selfadjoint g e eps P hg heLower he heps.le hsmall hd)
    (onePhononSchurCoercivityConstant_pos heps) (onePhononSchurOperator_coercive g e eps P hg heLower he heps hsmall hd hd0 hc hzero)

theorem onePhononSchurInverse_left :
    onePhononSchurInverse g e eps P hg heLower he heps hsmall hd hd0 hc hzero * (onePhononSchurOperator g e eps P hg heLower he heps.le hsmall hd) = 1 :=
  coerciveEnergyInverse_left (onePhononSchurOperator g e eps P hg heLower he heps.le hsmall hd) (onePhononSchurOperator_selfadjoint g e eps P hg heLower he heps.le hsmall hd)
    (onePhononSchurCoercivityConstant_pos heps) (onePhononSchurOperator_coercive g e eps P hg heLower he heps hsmall hd hd0 hc hzero)

theorem onePhononSchurInverse_right :
    (onePhononSchurOperator g e eps P hg heLower he heps.le hsmall hd) * onePhononSchurInverse g e eps P hg heLower he heps hsmall hd hd0 hc hzero = 1 :=
  coerciveEnergyInverse_right (onePhononSchurOperator g e eps P hg heLower he heps.le hsmall hd) (onePhononSchurOperator_selfadjoint g e eps P hg heLower he heps.le hsmall hd)
    (onePhononSchurCoercivityConstant_pos heps) (onePhononSchurOperator_coercive g e eps P hg heLower he heps hsmall hd hd0 hc hzero)

theorem onePhononSchurInverse_norm_le :
    ‖onePhononSchurInverse g e eps P hg heLower he heps hsmall hd hd0 hc hzero‖ ≤ (onePhononSchurCoercivityConstant eps)⁻¹ :=
  coerciveEnergyInverse_norm_le (onePhononSchurOperator g e eps P hg heLower he heps.le hsmall hd) (onePhononSchurOperator_selfadjoint g e eps P hg heLower he heps.le hsmall hd)
    (onePhononSchurCoercivityConstant_pos heps) (onePhononSchurOperator_coercive g e eps P hg heLower he heps hsmall hd hd0 hc hzero)

end Froehlich
