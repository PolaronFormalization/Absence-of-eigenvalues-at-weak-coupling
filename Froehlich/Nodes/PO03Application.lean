import Froehlich.Nodes.OP02
import Froehlich.Nodes.PO01

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

/-- Apply the proved two-vector criterion to the actual translated form at nonzero momentum. -/
theorem translatedThresholdForm_nonnegative_of_criterion
    (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (CD : ℝ) (hCD : 0 ≤ CD)
    (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2)
    (hquarter : |g| ≤ 1/4) (heLower : -sectorEnergyConstant*|g|^2 ≤ e)
    (hquadratic : sectorQuadraticConstant*|g|^2 ≤ 1/8)
    (P : GW.Space) (hP : ‖P‖ ≤ 1/4) (hP0 : P ≠ 0)
    (hN : ‖thresholdBoundedOperator e he g hg hs CD hCD hquad P hP-1‖ ≤ 1/2) :
    let B := thresholdBoundedOperator e he g hg hs CD hCD hquad P hP
    let R := thresholdBoundedInverse e he g hg hs CD hCD hquad P hP
    let b := thresholdKernelSourceVector e he g hg hs P hP
    let t := translatedHilbertSource g P hP0
    1+⟪b,R t⟫_ℂ ≠ 0 →
    0 ≤ ‖1+⟪b,R t⟫_ℂ‖^2+(⟪t,R t⟫_ℂ).re*
      (kernelConstant e he g hg hs P-(⟪b,R b⟫_ℂ).re) →
    ∀ f : OneParticleEnergySpace 0,
      0 ≤ (translatedThresholdForm e he g hquarter heLower hquadratic P hP f f).re := by
  dsimp only
  intro hne hcriterion f
  let B := thresholdBoundedOperator e he g hg hs CD hCD hquad P hP
  let R := thresholdBoundedInverse e he g hg hs CD hCD hquad P hP
  let b := thresholdKernelSourceVector e he g hg hs P hP
  let t := translatedHilbertSource g P hP0
  have hB : B.adjoint = B := thresholdBoundedOperator_selfadjoint e he g hg hs CD hCD hquad P hP
  have hp (u : GW.OnePhonon) : (1/2 : ℝ)*‖u‖^2 ≤ (⟪u,B u⟫_ℂ).re := by
    simpa only [div_eq_mul_inv,one_mul,mul_comm] using
      thresholdBoundedOperator_quadratic_lower e he g hg hs CD hCD hquad P hP hN u
  have hR : R = coerciveEnergyInverse B hB (by norm_num : (0 : ℝ) < 1/2) hp :=
    coerciveEnergyInverse_unique B R hB (by norm_num) hp
      (thresholdBoundedInverse_spec e he g hg hs CD hCD hquad P hP hN).1
  have hpos := twoVector_positivity B hB (1/2) (by norm_num) hp b t
    (kernelConstant e he g hg hs P)
  dsimp only at hpos
  rw [←hR] at hpos
  have hout := hpos hne hcriterion (oneParticleRadialMap f)
  rw [twoVectorForm_diagonal] at hout
  rw [translatedThresholdForm_unnormalized_real e he g hg hs CD hCD hquad hquarter heLower hquadratic P hP,
    translatedLinearSource_eq_hilbert_radial g P hP0]
  exact hout

end Froehlich
