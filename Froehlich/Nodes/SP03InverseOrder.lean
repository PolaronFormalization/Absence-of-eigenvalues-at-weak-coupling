import Froehlich.Nodes.SP03PhysicalInverse

/-! SP03: positivity and inverse order on actual high-sector dual sources.
This is the source variational argument, reused from BA02. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

variable (g e : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (heLower : -sectorEnergyConstant*|g|^2 ≤ e) (he : e ≤ 0)
    (hsmall : sectorQuadraticConstant*|g|^2 ≤ 1/8)

include hg heLower he hsmall in
theorem twoSectorOperator_nonnegative (eps : ℝ) (heps : 0 ≤ eps)
    (u : HighEnergySpace P 2) :
    0 ≤ (⟪u,twoSectorOperator g P (e+1-eps) u⟫_ℂ).re := by
  let d := twoSectorCoercivity g e eps P hg heLower he heps hsmall
  exact (mul_nonneg d.positive.le (sq_nonneg ‖u‖)).trans (d.bound u)

theorem twoSectorEnergyInverse_nonnegative (eps : ℝ) (heps : 0 ≤ eps)
    (z : HighEnergySpace P 2) :
    0 ≤ (⟪z,twoSectorEnergyInverse g e eps P hg heLower he heps hsmall z⟫_ℂ).re :=
  inverse_nonnegative _ _ (twoSectorOperator_selfadjoint g P (e+1-eps))
    (twoSectorEnergyInverse_right_apply g e eps P hg heLower he heps hsmall)
    (twoSectorOperator_nonnegative g e P hg heLower he hsmall eps heps) z

theorem twoSectorEnergyInverse_decreasing (eps1 eps2 : ℝ)
    (h1 : 0 ≤ eps1) (h12 : eps1 ≤ eps2) (z : HighEnergySpace P 2) :
    (⟪z,twoSectorEnergyInverse g e eps2 P hg heLower he (h1.trans h12) hsmall z⟫_ℂ).re ≤
      (⟪z,twoSectorEnergyInverse g e eps1 P hg heLower he h1 hsmall z⟫_ℂ).re := by
  apply inverse_order (twoSectorOperator g P (e+1-eps1))
    (twoSectorOperator g P (e+1-eps2))
    (twoSectorEnergyInverse g e eps1 P hg heLower he h1 hsmall)
    (twoSectorEnergyInverse g e eps2 P hg heLower he (h1.trans h12) hsmall)
    (twoSectorOperator_selfadjoint g P _) (twoSectorOperator_selfadjoint g P _)
    (twoSectorEnergyInverse_right_apply g e eps1 P hg heLower he h1 hsmall)
    (twoSectorEnergyInverse_right_apply g e eps2 P hg heLower he (h1.trans h12) hsmall)
    (twoSectorOperator_nonnegative g e P hg heLower he hsmall eps1 h1)
    (twoSectorOperator_nonnegative g e P hg heLower he hsmall eps2 (h1.trans h12))
  intro u
  change (⟪u,sourceOperator (twoSectorBaseOperator g P) (highEnergyEmbedding P 2)
      (e+1-eps1) u⟫_ℂ).re ≤
    (⟪u,sourceOperator (twoSectorBaseOperator g P) (highEnergyEmbedding P 2)
      (e+1-eps2) u⟫_ℂ).re
  rw [sourceOperator_quadratic,sourceOperator_quadratic]
  have hm := mul_le_mul_of_nonneg_right h12 (sq_nonneg ‖highEnergyEmbedding P 2 u‖)
  nlinarith

theorem twoSectorPhysicalInverse_nonnegative (eps : ℝ) (heps : 0 ≤ eps)
    (f : HighSectorSpace 2) :
    0 ≤ (⟪f,twoSectorPhysicalInverse g e eps P hg heLower he heps hsmall f⟫_ℂ).re := by
  change 0 ≤ (⟪f,highEnergyEmbedding P 2
    (twoSectorEnergyInverse g e eps P hg heLower he heps hsmall
      ((highEnergyEmbedding P 2).adjoint f))⟫_ℂ).re
  rw [← (highEnergyEmbedding P 2).adjoint_inner_left]
  exact twoSectorEnergyInverse_nonnegative g e P hg heLower he hsmall eps heps _

end Froehlich
