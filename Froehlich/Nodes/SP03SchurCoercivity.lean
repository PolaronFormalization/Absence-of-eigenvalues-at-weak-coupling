import Froehlich.Nodes.SP03SchurBounds
import Froehlich.Nodes.SP03SchurMonotone
import Froehlich.Nodes.SP03SchurSelfadjoint
import Froehlich.Nodes.FA03

/-! Source interpolation produces coercivity in the full isolated energy norm. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

def onePhononSchurCoercivityConstant (eps : ℝ) : ℝ :=
  min (eps/(2*(1/2+eps))*(1/2)) (eps/2)

theorem onePhononSchurCoercivityConstant_pos {eps : ℝ} (h : 0 < eps) :
    0 < onePhononSchurCoercivityConstant eps := by
  unfold onePhononSchurCoercivityConstant
  apply lt_min <;> positivity

variable (g e eps : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (heLower : -sectorEnergyConstant*|g|^2 ≤ e) (he : e ≤ 0)
    (heps : 0 < eps) (hsmall : sectorQuadraticConstant*|g|^2 ≤ 1/8)

theorem onePhononSchurOperator_coercive
    (hd : 1/2 ≤ onePhononVacuumDenominator e eps P)
    (hd0 : 1/2 ≤ onePhononVacuumDenominator e 0 P)
    (hc : onePhononCorrectionConstant*|g|^2 ≤ 1/2)
    (hzero : ∀ f : OneParticleEnergySpace P,
      0 ≤ (⟪f,onePhononSchurOperator g e 0 P hg heLower he (by norm_num) hsmall hd0 f⟫_ℂ).re)
    (f : OneParticleEnergySpace P) :
    onePhononSchurCoercivityConstant eps * ‖f‖^2 ≤
      (⟪f,onePhononSchurOperator g e eps P hg heLower he heps.le hsmall hd f⟫_ℂ).re := by
  have hm := onePhononSchurOperator_monotone g e eps P hg heLower he heps.le hsmall hd hd0 f
  have hz := hzero f
  have hgph := onePhononSchurOperator_graph_lower g e eps P hg heLower he heps.le hsmall hd hc f
  have hint := graph_coercivity_interpolation heps (by norm_num : (0:ℝ)<1/2)
    (by norm_num : (0:ℝ)≤1/2) (show eps*‖oneParticleEnergyEmbedding P f‖^2 ≤
      (⟪f,onePhononSchurOperator g e eps P hg heLower he heps.le hsmall hd f⟫_ℂ).re by linarith) hgph
  have hk := mul_le_mul_of_nonneg_right
    (min_le_left (eps/(2*(1/2+eps))*(1/2)) (eps/2)) (sq_nonneg (onePhononKineticNorm P f))
  have hmass := mul_le_mul_of_nonneg_right
    (min_le_right (eps/(2*(1/2+eps))*(1/2)) (eps/2)) (sq_nonneg ‖oneParticleEnergyEmbedding P f‖)
  rw [onePhononKineticNorm_identity]
  unfold onePhononSchurCoercivityConstant
  nlinarith

end Froehlich
