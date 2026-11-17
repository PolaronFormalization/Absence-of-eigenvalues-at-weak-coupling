import Froehlich.Nodes.SP01Inverse

/-! SP03: the actual two-phonon compressed form representative and its
energy inverse with the exact source bound eight. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

def twoSectorBaseOperator (g : ℝ) (P : GW.Space) : HighEnergySpace P 2 →L[ℂ] HighEnergySpace P 2 :=
  GW.Operators.formRiesz (compressedFiberFormData g P 2 none) -
    ((compressedFiberFormData g P 2 none).shift : ℂ) •
      ((highEnergyEmbedding P 2).adjoint.comp (highEnergyEmbedding P 2))

def twoSectorOperator (g : ℝ) (P : GW.Space) (lam : ℝ) : HighEnergySpace P 2 →L[ℂ] HighEnergySpace P 2 :=
  sourceOperator (twoSectorBaseOperator g P) (highEnergyEmbedding P 2) lam

theorem twoSectorBaseOperator_selfadjoint (g : ℝ) (P : GW.Space) :
    (twoSectorBaseOperator g P).adjoint = twoSectorBaseOperator g P := by
  simp only [twoSectorBaseOperator,map_sub,map_smulₛₗ,ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint,Complex.conj_ofReal,(GW.Operators.formRiesz_spec _).2.1]

theorem twoSectorOperator_selfadjoint (g : ℝ) (P : GW.Space) (lam : ℝ) :
    (twoSectorOperator g P lam).adjoint = twoSectorOperator g P lam :=
  sourceOperator_selfadjoint _ _ (twoSectorBaseOperator_selfadjoint g P) lam

theorem twoSectorOperator_spec (g : ℝ) (P : GW.Space) (lam : ℝ) (w u : HighEnergySpace P 2) :
    ⟪w,twoSectorOperator g P lam u⟫_ℂ = (compressedFiberFormData g P 2 none).form w u -
      (lam : ℂ)*⟪highEnergyEmbedding P 2 w,highEnergyEmbedding P 2 u⟫_ℂ := by
  simp only [twoSectorOperator,sourceOperator,twoSectorBaseOperator,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,inner_sub_right,inner_smul_right]
  rw [← (GW.Operators.formRiesz_spec (compressedFiberFormData g P 2 none)).1]
  simp only [(highEnergyEmbedding P 2).adjoint_inner_right]
  rw [GW.Operators.energyForm,GW.Operators.shiftedForm_apply]
  have he : (compressedFiberFormData g P 2 none).embedding = highEnergyEmbedding P 2 := rfl
  rw [he]
  ring


def twoSectorCoercivity (g e eps : ℝ) (P : GW.Space)
    (hg : |g| ≤ 1/4) (heLower : -sectorEnergyConstant*|g|^2 ≤ e)
    (he : e ≤ 0) (heps : 0 ≤ eps) (hsmall : sectorQuadraticConstant*|g|^2 ≤ 1/8) :
    CompressedCoercivity g (e+1-eps) P 2 none where
  operator := twoSectorOperator g P (e+1-eps)
  selfadjoint := twoSectorOperator_selfadjoint g P (e+1-eps)
  lower := 1/8
  positive := by norm_num
  representative := twoSectorOperator_spec g P (e+1-eps)
  bound u := by
    have h := fiberForm_twoSector_energy_lower g e eps P u hg heLower he heps hsmall
    have hi : (⟪highEnergyEmbedding P 2 u,highEnergyEmbedding P 2 u⟫_ℂ).re =
        ‖energyEmbedding P (u : EnergySpace P)‖^2 := by
      change (⟪(highEnergyEmbedding P 2 u : GW.Fock.Carrier),
        (highEnergyEmbedding P 2 u : GW.Fock.Carrier)⟫_ℂ).re = _
      simp only [highEnergyEmbedding_apply]
      simpa only [RCLike.re_eq_complex_re] using
        (norm_sq_eq_re_inner (𝕜 := ℂ) (energyEmbedding P (u : EnergySpace P))).symm
    rw [twoSectorOperator_spec,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero,hi]
    exact h

def twoSectorEnergyInverse (g e eps : ℝ) (P : GW.Space)
    (hg : |g| ≤ 1/4) (heLower : -sectorEnergyConstant*|g|^2 ≤ e)
    (he : e ≤ 0) (heps : 0 ≤ eps) (hsmall : sectorQuadraticConstant*|g|^2 ≤ 1/8) :
    HighEnergySpace P 2 →L[ℂ] HighEnergySpace P 2 :=
  let d := twoSectorCoercivity g e eps P hg heLower he heps hsmall
  coerciveEnergyInverse d.operator d.selfadjoint d.positive d.bound

theorem twoSectorEnergyInverse_norm_le (g e eps : ℝ) (P : GW.Space)
    (hg : |g| ≤ 1/4) (heLower : -sectorEnergyConstant*|g|^2 ≤ e)
    (he : e ≤ 0) (heps : 0 ≤ eps) (hsmall : sectorQuadraticConstant*|g|^2 ≤ 1/8) :
    ‖twoSectorEnergyInverse g e eps P hg heLower he heps hsmall‖ ≤ 8 := by
  let d := twoSectorCoercivity g e eps P hg heLower he heps hsmall
  have h := coerciveEnergyInverse_norm_le d.operator d.selfadjoint d.positive d.bound
  change ‖twoSectorEnergyInverse g e eps P hg heLower he heps hsmall‖ ≤ (1/8 : ℝ)⁻¹ at h
  norm_num at h
  exact h

end Froehlich
