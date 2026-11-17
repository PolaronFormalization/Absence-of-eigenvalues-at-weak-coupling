import Froehlich.Nodes.RS02SourceEnergy

set_option autoImplicit false

/-! RS03's entirely bounded zeroth-order self-energy formula and uniform
quadratic bound. No parameter regularity or Hessian statement is claimed. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem rs03NormalizedInverse_selfadjoint (g : ℝ) (n : ℕ) (e : ℝ) (p : GW.Space)
    (he : e ≤ 0) (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant*|g| ≤ 1/2) :
    (auxiliaryNormalizedInverse g n e p he hg hsmall).adjoint =
      auxiliaryNormalizedInverse g n e p he hg hsmall :=
  inverse_selfadjoint _ _ (auxiliaryNormalizedOperator_selfadjoint g n e p he)
    (auxiliaryNormalizedInverse_left g n e p he hg hsmall)
    (auxiliaryNormalizedInverse_right g n e p he hg hsmall)

theorem auxiliarySource_inverse_inner_real (g e : ℝ) (p : GW.Space) (he : e ≤ 0)
    (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant*|g| ≤ 1/2) :
    (⟪auxiliaryNormalizedSource g e p he,
      auxiliaryNormalizedInverse g 1 e p he hg hsmall (auxiliaryNormalizedSource g e p he)⟫_ℂ).im = 0 := by
  let z := auxiliaryNormalizedSource g e p he
  let Q := auxiliaryNormalizedInverse g 1 e p he hg hsmall
  have hQ : Q.adjoint = Q := rs03NormalizedInverse_selfadjoint g 1 e p he hg hsmall
  have hs : ⟪Q z,z⟫_ℂ = ⟪z,Q z⟫_ℂ := by
    simpa only [hQ] using Q.adjoint_inner_left z z
  have hi := congrArg Complex.im hs
  have hc := congrArg Complex.im (inner_conj_symm (𝕜 := ℂ) z (Q z))
  simp only [Complex.conj_im] at hc
  change (⟪z,Q z⟫_ℂ).im = 0
  linarith

variable (e : ℝ) (p : GW.Space) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant*|g| ≤ 1/2)

theorem auxiliaryGroundSourceEnergy_bounded_pairing :
    highFiberSourceLoad g (-p) 1 (auxiliaryGroundSourceEnergy e p he g hg hsmall) =
      ⟪auxiliaryNormalizedSource g e p he.2,
        auxiliaryNormalizedInverse g 1 e p he.2 hg hsmall (auxiliaryNormalizedSource g e p he.2)⟫_ℂ := by
  let z := auxiliaryNormalizedSource g e p he.2
  let Q := auxiliaryNormalizedInverse g 1 e p he.2 hg hsmall
  rw [auxiliaryGroundSourceEnergy_formula]
  change fiberSourceLoad g (-p)
    (auxiliaryEnergyLiftEquivalence 1 e p (by norm_num) he (Q z) : EnergySpace (-p)) = _
  rw [auxiliaryEnergyLiftEquivalence_val]
  have hp := (auxiliaryNormalizedSource_pairing g e p he.2 (Q z)).symm
  have hQ : Q.adjoint = Q := rs03NormalizedInverse_selfadjoint g 1 e p he.2 hg hsmall
  have hs : ⟪Q z,z⟫_ℂ = ⟪z,Q z⟫_ℂ := by
    simpa only [hQ] using Q.adjoint_inner_left z z
  exact hp.trans hs

theorem auxiliarySelfEnergy_bounded_formula :
    auxiliarySelfEnergy e p he g hg hsmall =
      -(⟪auxiliaryNormalizedSource g e p he.2,
        auxiliaryNormalizedInverse g 1 e p he.2 hg hsmall (auxiliaryNormalizedSource g e p he.2)⟫_ℂ).re := by
  unfold auxiliarySelfEnergy
  rw [auxiliaryGroundSourceEnergy_bounded_pairing e p he g hg hsmall]

theorem auxiliarySelfEnergy_bounded_complex :
    (auxiliarySelfEnergy e p he g hg hsmall : ℂ) =
      -⟪auxiliaryNormalizedSource g e p he.2,
        auxiliaryNormalizedInverse g 1 e p he.2 hg hsmall (auxiliaryNormalizedSource g e p he.2)⟫_ℂ := by
  apply Complex.ext
  · simp only [Complex.ofReal_re,Complex.neg_re,auxiliarySelfEnergy_bounded_formula]
  · simp only [Complex.ofReal_im,Complex.neg_im,
      auxiliarySource_inverse_inner_real g e p he.2 hg hsmall,neg_zero]

theorem auxiliarySelfEnergy_uniform_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (g e : ℝ) (p : GW.Space) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
      (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant*|g| ≤ 1/2),
      |auxiliarySelfEnergy e p he g hg hsmall| ≤ C*g^2 := by
  obtain ⟨Cz,hCz,hz⟩ := auxiliaryNormalizedSources_uniform_bound
  refine ⟨2*Cz,by positivity,?_⟩
  intro g e p he hg hsmall
  let z := auxiliaryNormalizedSource g e p he.2
  let Q := auxiliaryNormalizedInverse g 1 e p he.2 hg hsmall
  have hQz : ‖Q z‖ ≤ 2*‖z‖ := (Q.le_opNorm z).trans
    (mul_le_mul_of_nonneg_right (auxiliaryNormalizedInverse_norm_le g 1 e p he.2 hg hsmall) (norm_nonneg z))
  rw [auxiliarySelfEnergy_bounded_formula e p he g hg hsmall,abs_neg]
  calc
    _ ≤ ‖⟪z,Q z⟫_ℂ‖ := Complex.abs_re_le_norm _
    _ ≤ ‖z‖*‖Q z‖ := norm_inner_le_norm z (Q z)
    _ ≤ ‖z‖*(2*‖z‖) := mul_le_mul_of_nonneg_left hQz (norm_nonneg z)
    _ = 2*‖z‖^2 := by ring
    _ ≤ 2*(Cz*g^2) := mul_le_mul_of_nonneg_left (hz g e p he.2) (by norm_num)
    _ = _ := by ring

end Froehlich
