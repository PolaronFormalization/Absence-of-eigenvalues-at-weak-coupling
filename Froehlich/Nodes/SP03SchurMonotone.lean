import Froehlich.Nodes.SP03SchurForm

/-! Monotonicity on all original one-particle energy vectors. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich
variable (g e eps : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (heLower : -sectorEnergyConstant*|g|^2 ≤ e) (he : e ≤ 0)
    (heps : 0 ≤ eps) (hsmall : sectorQuadraticConstant*|g|^2 ≤ 1/8)

theorem onePhononSchurOperator_monotone
    (hd : 1/2 ≤ onePhononVacuumDenominator e eps P)
    (hd0 : 1/2 ≤ onePhononVacuumDenominator e 0 P)
    (f : OneParticleEnergySpace P) :
    eps * ‖oneParticleEnergyEmbedding P f‖^2 +
      (⟪f,onePhononSchurOperator g e 0 P hg heLower he (by norm_num) hsmall hd0 f⟫_ℂ).re ≤
      (⟪f,onePhononSchurOperator g e eps P hg heLower he heps hsmall hd f⟫_ℂ).re := by
  rw [onePhononSchurOperator_diagonal,onePhononSchurOperator_diagonal]
  have hD := twoSectorEnergyInverse_decreasing g e P hg heLower he hsmall 0 eps
    (by norm_num) heps (twoSectorCoupling g P f)
  rw [← onePhononHighCorrection_spec,← onePhononHighCorrection_spec] at hD
  have hp : 0 < onePhononVacuumDenominator e eps P := by linarith
  have horder : onePhononVacuumDenominator e eps P ≤ onePhononVacuumDenominator e 0 P := by
    unfold onePhononVacuumDenominator
    linarith
  have hi := one_div_le_one_div_of_le hp horder
  have hs := mul_le_mul_of_nonneg_left hi (sq_nonneg ‖onePhononSourceLinear g P f‖)
  simp only [div_eq_mul_inv,one_mul] at hs ⊢
  linarith

end Froehlich
