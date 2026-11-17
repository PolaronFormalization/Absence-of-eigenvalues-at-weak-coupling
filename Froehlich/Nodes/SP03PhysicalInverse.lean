import Froehlich.Nodes.SP03HighInverse

/-! SP03: the exact weak equation and physical high-sector inverse bound
four, obtained from the actual mass lower bound rather than the graph norm. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

variable (g e eps : ℝ) (P : GW.Space)
    (hg : |g| ≤ 1/4) (heLower : -sectorEnergyConstant*|g|^2 ≤ e)
    (he : e ≤ 0) (heps : 0 ≤ eps) (hsmall : sectorQuadraticConstant*|g|^2 ≤ 1/8)

theorem twoSectorEnergyInverse_right_apply (u : HighEnergySpace P 2) :
    twoSectorOperator g P (e+1-eps)
      (twoSectorEnergyInverse g e eps P hg heLower he heps hsmall u) = u := by
  let d := twoSectorCoercivity g e eps P hg heLower he heps hsmall
  exact congrArg (fun T : HighEnergySpace P 2 →L[ℂ] HighEnergySpace P 2 => T u)
    (coerciveEnergyInverse_right d.operator d.selfadjoint d.positive d.bound)

theorem twoSectorEnergyInverse_left_apply (u : HighEnergySpace P 2) :
    twoSectorEnergyInverse g e eps P hg heLower he heps hsmall
      (twoSectorOperator g P (e+1-eps) u) = u := by
  let d := twoSectorCoercivity g e eps P hg heLower he heps hsmall
  exact congrArg (fun T : HighEnergySpace P 2 →L[ℂ] HighEnergySpace P 2 => T u)
    (coerciveEnergyInverse_left d.operator d.selfadjoint d.positive d.bound)

def twoSectorPhysicalInverse : HighSectorSpace 2 →L[ℂ] HighSectorSpace 2 :=
  (highEnergyEmbedding P 2).comp
    ((twoSectorEnergyInverse g e eps P hg heLower he heps hsmall).comp
      (highEnergyEmbedding P 2).adjoint)

theorem twoSectorPhysicalInverse_weak (f : HighSectorSpace 2) (w : HighEnergySpace P 2) :
    let u := twoSectorEnergyInverse g e eps P hg heLower he heps hsmall
      ((highEnergyEmbedding P 2).adjoint f)
    (compressedFiberFormData g P 2 none).form w u -
      ((e+1-eps : ℝ) : ℂ)*⟪highEnergyEmbedding P 2 w,highEnergyEmbedding P 2 u⟫_ℂ =
      ⟪highEnergyEmbedding P 2 w,f⟫_ℂ := by
  dsimp only
  rw [← twoSectorOperator_spec,twoSectorEnergyInverse_right_apply]
  exact (highEnergyEmbedding P 2).adjoint_inner_right w f

theorem twoSectorPhysicalInverse_norm_le :
    ‖twoSectorPhysicalInverse g e eps P hg heLower he heps hsmall‖ ≤ 4 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  let u := twoSectorEnergyInverse g e eps P hg heLower he heps hsmall
    ((highEnergyEmbedding P 2).adjoint f)
  have hm := fiberForm_twoSector_mass_lower g e eps P u hg heLower he heps hsmall
  have hi : (⟪highEnergyEmbedding P 2 u,highEnergyEmbedding P 2 u⟫_ℂ).re =
      ‖energyEmbedding P (u : EnergySpace P)‖^2 := by
    change (⟪(highEnergyEmbedding P 2 u : GW.Fock.Carrier),
      (highEnergyEmbedding P 2 u : GW.Fock.Carrier)⟫_ℂ).re = _
    simp only [highEnergyEmbedding_apply]
    simpa only [RCLike.re_eq_complex_re] using
      (norm_sq_eq_re_inner (𝕜 := ℂ) (energyEmbedding P (u : EnergySpace P))).symm
  have hw := congrArg Complex.re
    (twoSectorPhysicalInverse_weak g e eps P hg heLower he heps hsmall f u)
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] at hw
  change ((fiberFormData g P none).form (u : EnergySpace P) (u : EnergySpace P)).re -
    (e+1-eps)*(⟪highEnergyEmbedding P 2 u,highEnergyEmbedding P 2 u⟫_ℂ).re =
      (⟪highEnergyEmbedding P 2 u,f⟫_ℂ).re at hw
  rw [hi] at hw
  have hcs := (Complex.re_le_norm (⟪highEnergyEmbedding P 2 u,f⟫_ℂ)).trans
    (norm_inner_le_norm (𝕜 := ℂ) (highEnergyEmbedding P 2 u) f)
  have hn : ‖highEnergyEmbedding P 2 u‖ = ‖energyEmbedding P (u : EnergySpace P)‖ := rfl
  rw [hn] at hcs
  change ‖energyEmbedding P (u : EnergySpace P)‖ ≤ 4*‖f‖
  by_cases hz : ‖energyEmbedding P (u : EnergySpace P)‖ = 0
  · rw [hz]
    positivity
  · have hp := lt_of_le_of_ne (norm_nonneg (energyEmbedding P (u : EnergySpace P))) (Ne.symm hz)
    nlinarith

end Froehlich
