import Froehlich.Nodes.SP03SchurForm

/-! The source graph lower bound on the actual one-particle energy domain. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich
variable (g e eps : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (heLower : -sectorEnergyConstant*|g|^2 ≤ e) (he : e ≤ 0)
    (heps : 0 ≤ eps) (hsmall : sectorQuadraticConstant*|g|^2 ≤ 1/8)

theorem onePhononSchurOperator_graph_lower
    (hd : 1/2 ≤ onePhononVacuumDenominator e eps P)
    (hc : onePhononCorrectionConstant*|g|^2 ≤ 1/2)
    (f : OneParticleEnergySpace P) :
    1/2 * onePhononKineticNorm P f ^ 2 -
      1/2 * ‖oneParticleEnergyEmbedding P f‖^2 ≤
      (⟪f,onePhononSchurOperator g e eps P hg heLower he heps hsmall hd f⟫_ℂ).re := by
  rw [onePhononSchurOperator_diagonal]
  have hD := onePhononHighCorrection_bound g e eps P hg heLower he heps hsmall f
  have hb := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖f‖)
  rw [onePhononKineticNorm_identity] at hD hb
  have hm : 0 ≤ (eps-e)*‖oneParticleEnergyEmbedding P f‖^2 :=
    mul_nonneg (sub_nonneg.mpr (he.trans heps)) (sq_nonneg _)
  have hs : 0 ≤ ‖onePhononSourceLinear g P f‖^2/onePhononVacuumDenominator e eps P :=
    div_nonneg (sq_nonneg _) (by linarith)
  linarith

end Froehlich
