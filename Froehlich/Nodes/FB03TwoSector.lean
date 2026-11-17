import Froehlich.Nodes.FB03Nonvacuum

/-! The source two-sector lower bounds, with exactly C₂=4C_L and the
separate smallness condition C₂|g|²≤1/8. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem fiberForm_quarter_lower (g e eps : ℝ) (P : GW.Space) (u : EnergySpace P)
    (hg : |g| ≤ 1/4) (he : e ≤ 0) (heps : 0 ≤ eps) :
    (3/4 : ℝ)*freeEnergy P (energyEmbedding P u) -
      (1+sectorQuadraticConstant*|g|^2)*‖energyEmbedding P u‖^2 ≤
        ((fiberFormData g P none).form u u).re - (e+1-eps)*‖energyEmbedding P u‖^2 := by
  have hb := singular_liebYamazaki_small g P u (1/4 : ℝ) (by norm_num) (by norm_num) hg
  have hl := neg_le_of_abs_le ((Complex.abs_re_le_norm (singularInteraction g P u u)).trans hb)
  have he' := mul_nonpos_of_nonpos_of_nonneg he (sq_nonneg ‖energyEmbedding P u‖)
  have heps' := mul_nonneg heps (sq_nonneg ‖energyEmbedding P u‖)
  rw [fiberFormData_singular_apply,Complex.add_re,freeFiberForm_physical_energy]
  dsimp only [sectorQuadraticConstant]
  rw [sq_abs]
  nlinarith

theorem fiberForm_twoSector_energy_lower (g e eps : ℝ) (P : GW.Space) (u : HighEnergySpace P 2)
    (hg : |g| ≤ 1/4) (_heLower : -sectorEnergyConstant*|g|^2 ≤ e)
    (he : e ≤ 0) (heps : 0 ≤ eps) (hsmall : sectorQuadraticConstant*|g|^2 ≤ 1/8) :
    (1/8 : ℝ)*‖u‖^2 ≤
      ((fiberFormData g P none).form u u).re - (e+1-eps)*‖energyEmbedding P (u : EnergySpace P)‖^2 := by
  have hb := fiberForm_quarter_lower g e eps P (u : EnergySpace P) hg he heps
  have hN := highEnergy_number_lower P 2 u
  have hk := energyKineticNorm_number_identity P (u : EnergySpace P)
  change energyKineticNorm P u ^ 2 + energyNumberExpectation P u = _ at hk
  have hn : ‖u‖^2 = ‖energyEmbedding P (u : EnergySpace P)‖^2 +
      freeEnergy P (energyEmbedding P (u : EnergySpace P)) :=
    energyEmbedding_norm_identity P (u : EnergySpace P)
  have hm := mul_nonneg (show 0 ≤ (1/8 : ℝ)-sectorQuadraticConstant*|g|^2 by linarith)
    (sq_nonneg ‖energyEmbedding P (u : EnergySpace P)‖)
  norm_num only [Nat.cast_ofNat] at hN
  nlinarith [sq_nonneg (energyKineticNorm P (u : EnergySpace P))]

theorem fiberForm_twoSector_mass_lower (g e eps : ℝ) (P : GW.Space) (u : HighEnergySpace P 2)
    (hg : |g| ≤ 1/4) (_heLower : -sectorEnergyConstant*|g|^2 ≤ e)
    (he : e ≤ 0) (heps : 0 ≤ eps) (hsmall : sectorQuadraticConstant*|g|^2 ≤ 1/8) :
    (1/4 : ℝ)*‖energyEmbedding P (u : EnergySpace P)‖^2 ≤
      ((fiberFormData g P none).form u u).re - (e+1-eps)*‖energyEmbedding P (u : EnergySpace P)‖^2 := by
  have hb := fiberForm_quarter_lower g e eps P (u : EnergySpace P) hg he heps
  have hN := highEnergy_number_lower P 2 u
  have hk := energyKineticNorm_number_identity P (u : EnergySpace P)
  change energyKineticNorm P u ^ 2 + energyNumberExpectation P u = _ at hk
  have hm := mul_nonneg (show 0 ≤ (1/8 : ℝ)-sectorQuadraticConstant*|g|^2 by linarith)
    (sq_nonneg ‖energyEmbedding P (u : EnergySpace P)‖)
  norm_num only [Nat.cast_ofNat] at hN
  nlinarith [sq_nonneg (energyKineticNorm P (u : EnergySpace P)),
    sq_nonneg ‖energyEmbedding P (u : EnergySpace P)‖]

end Froehlich
