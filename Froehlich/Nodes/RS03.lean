import Froehlich.Nodes.RS03DerivativesHessian
import Froehlich.Nodes.RS03StaticBounded
import Froehlich.Nodes.RS03StaticReflection
import Froehlich.Nodes.RS03Smooth
import Froehlich.Nodes.RS01
import Froehlich.Nodes.CA03Even

set_option autoImplicit false

/-! RS03 / lem:selfenergy. The Hessian and quadratic bounds are for the
actual bounded self-energy, with one constant chosen before coupling. -/
noncomputable section
namespace Froehlich

def RS03Quantitative (C e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2) : Prop :=
  (∀ p : GW.Space, (auxiliarySelfEnergy e p he g hg hs : ℂ) =
    -highFiberSourceLoad g (-p) 1 (auxiliaryGroundSourceEnergy e p he g hg hs)) ∧
  Function.Even (fun p : GW.Space => auxiliarySelfEnergy e p he g hg hs) ∧
  ContDiff ℝ 2 (fun p : GW.Space => auxiliarySelfEnergy e p he g hg hs) ∧
  (∀ p : GW.Space, ‖fderiv ℝ (fderiv ℝ (fun q : GW.Space => auxiliarySelfEnergy e q he g hg hs)) p‖ ≤ C*g^2) ∧
  (∀ p : GW.Space, |auxiliarySelfEnergy e p he g hg hs| ≤ C*g^2) ∧
  auxiliarySelfEnergy e 0 he g hg hs = e ∧
  (∀ p : GW.Space, |auxiliarySelfEnergy e p he g hg hs-e| ≤ C*g^2*‖p‖^2)

theorem finalRS03 : ∃ C s : ℝ, 0 < C ∧ 0 < s ∧ ∀ g : ℝ, |g| < s →
    ∃ he : groundEnergy (fiberHamiltonian g 0) ∈ Set.Icc (-1/4 : ℝ) 0,
    ∃ hg : |g| ≤ 1, ∃ hs : auxiliaryResolventConstant*|g| ≤ 1/2,
      RS03Quantitative C (groundEnergy (fiberHamiltonian g 0)) he g hg hs := by
  obtain ⟨CH,hCH,hHessian⟩ := auxiliarySelfEnergy_hessian_uniform
  obtain ⟨CA,hCA,hAbs⟩ := auxiliarySelfEnergy_uniform_bound
  obtain ⟨s,hs,hGround⟩ := auxiliarySelfEnergy_zero_groundEnergy
  let C := CH+CA+1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hHC : CH ≤ C := by dsimp only [C]; linarith
  have hAC : CA ≤ C := by dsimp only [C]; linarith
  refine ⟨C,s,hC,hs,?_⟩
  intro g hg
  obtain ⟨he,hg1,hsmall,hzero⟩ := hGround g hg
  let e := groundEnergy (fiberHamiltonian g 0)
  have heven : Function.Even (fun p : GW.Space => auxiliarySelfEnergy e p he g hg1 hsmall) :=
    fun p => auxiliarySelfEnergy_even e p he g hg1 hsmall
  have hdiff : ContDiff ℝ 2 (fun p : GW.Space => auxiliarySelfEnergy e p he g hg1 hsmall) :=
    auxiliarySelfEnergy_contDiff g e he hg1 hsmall
  have hh : ∀ p : GW.Space,
      ‖fderiv ℝ (fderiv ℝ (fun q : GW.Space => auxiliarySelfEnergy e q he g hg1 hsmall)) p‖ ≤ C*g^2 := by
    intro p
    exact (hHessian g e he hg1 hsmall p).trans (mul_le_mul_of_nonneg_right hHC (sq_nonneg g))
  refine ⟨he,hg1,hsmall,?_,heven,hdiff,hh,?_,hzero,?_⟩
  · intro p
    rw [auxiliarySelfEnergy_bounded_complex e p he g hg1 hsmall,
      auxiliaryGroundSourceEnergy_bounded_pairing e p he g hg1 hsmall]
  · intro p
    exact (hAbs g e p he hg1 hsmall).trans (mul_le_mul_of_nonneg_right hAC (sq_nonneg g))
  · intro p
    have hq := even_norm_sub_le_quadratic (fun q : GW.Space => auxiliarySelfEnergy e q he g hg1 hsmall)
      heven hdiff (C*g^2) hh p
    rw [hzero] at hq
    have hprod : 0 ≤ C*g^2*‖p‖^2 := mul_nonneg (mul_nonneg hC.le (sq_nonneg g)) (sq_nonneg _)
    exact hq.trans (by linarith)

end Froehlich
