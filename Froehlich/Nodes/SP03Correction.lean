import Froehlich.Nodes.SP03Coupling

/-! SP03's nonnegative high-sector Schur correction, with the literal
source constant sixteen times the square of the mixed-field constant. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

def onePhononCorrectionConstant : ℝ := 16*phiMixedConstant^2

variable (g e eps : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (heLower : -sectorEnergyConstant*|g|^2 ≤ e) (he : e ≤ 0)
    (heps : 0 ≤ eps) (hsmall : sectorQuadraticConstant*|g|^2 ≤ 1/8)

def onePhononHighCorrection : OneParticleEnergySpace P →L[ℂ] OneParticleEnergySpace P :=
  (twoSectorCoupling g P).adjoint.comp
    ((twoSectorEnergyInverse g e eps P hg heLower he heps hsmall).comp (twoSectorCoupling g P))

theorem onePhononHighCorrection_spec (f h : OneParticleEnergySpace P) :
    ⟪f,onePhononHighCorrection g e eps P hg heLower he heps hsmall h⟫_ℂ =
      ⟪twoSectorCoupling g P f,
        twoSectorEnergyInverse g e eps P hg heLower he heps hsmall (twoSectorCoupling g P h)⟫_ℂ := by
  rw [onePhononHighCorrection,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,
    (twoSectorCoupling g P).adjoint_inner_right]

theorem onePhononHighCorrection_nonnegative (f : OneParticleEnergySpace P) :
    0 ≤ (⟪f,onePhononHighCorrection g e eps P hg heLower he heps hsmall f⟫_ℂ).re := by
  rw [onePhononHighCorrection_spec]
  exact twoSectorEnergyInverse_nonnegative g e P hg heLower he hsmall eps heps _

theorem onePhononHighCorrection_bound (f : OneParticleEnergySpace P) :
    (⟪f,onePhononHighCorrection g e eps P hg heLower he heps hsmall f⟫_ℂ).re ≤
      onePhononCorrectionConstant*|g|^2*‖f‖^2 := by
  rw [onePhononHighCorrection_spec]
  let R := twoSectorEnergyInverse g e eps P hg heLower he heps hsmall
  let z := twoSectorCoupling g P f
  have hR : ‖R‖ ≤ 8 := twoSectorEnergyInverse_norm_le g e eps P hg heLower he heps hsmall
  have hRz : ‖R z‖ ≤ 8*‖z‖ := (R.le_opNorm z).trans
    (mul_le_mul_of_nonneg_right hR (norm_nonneg z))
  have hW := twoSectorCoupling_norm_le g P (hg.trans (by norm_num))
  have hz : ‖z‖ ≤ (Real.sqrt 2*phiMixedConstant*|g|)*‖f‖ :=
    ((twoSectorCoupling g P).le_opNorm f).trans
      (mul_le_mul_of_nonneg_right hW (norm_nonneg f))
  have hc := phiMixedConstant_pos
  have hsq : ‖z‖^2 ≤ ((Real.sqrt 2*phiMixedConstant*|g|)*‖f‖)^2 :=
    (sq_le_sq₀ (norm_nonneg z) (by positivity)).mpr hz
  have hinner := (Complex.re_le_norm (⟪z,R z⟫_ℂ)).trans (norm_inner_le_norm (𝕜 := ℂ) z (R z))
  change (⟪z,R z⟫_ℂ).re ≤ _
  calc
    _ ≤ 8*‖z‖^2 := hinner.trans (by
      calc
        ‖z‖*‖R z‖ ≤ ‖z‖*(8*‖z‖) := mul_le_mul_of_nonneg_left hRz (norm_nonneg z)
        _ = _ := by ring)
    _ ≤ 8*((Real.sqrt 2*phiMixedConstant*|g|)*‖f‖)^2 :=
      mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = _ := by
      rw [mul_pow,mul_pow,mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      dsimp only [onePhononCorrectionConstant]
      ring

end Froehlich
