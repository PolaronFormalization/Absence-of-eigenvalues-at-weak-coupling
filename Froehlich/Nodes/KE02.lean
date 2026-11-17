import Froehlich.Nodes.KE02ConstantQuadratic
import Froehlich.Nodes.KE02PsiBound
import Froehlich.Nodes.KE02RemainderBound
import Froehlich.Nodes.KE02RemainderDerivatives
import Froehlich.Nodes.RS01Anchors

set_option autoImplicit false

/-! KE02 / lem:kernelbounds. All six actual cancellation estimates, with
one constant before all parameters. No positivity or lower bound for c_P
is asserted; the kernel remainder is distinct from the vacuum scalar. -/
noncomputable section
namespace Froehlich

def KE02FixedReference (C e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2) : Prop :=
  (∀ P : GW.Space, ‖P‖ ≤ 1/4 →
    |kernelConstant e he g hg hs P-kernelConstant e he g hg hs 0| ≤ C*‖P‖^2 ∧
    (∀ q : GW.Space, |kernelPsi e he g hg hs P q| ≤ C*omega q*(omega q+‖P‖)) ∧
    (∀ q : GW.Space, |kernelPsi e he g hg hs P q-kernelPsi e he g hg hs 0 q| ≤ C*‖P‖*omega q) ∧
    (∀ q r : GW.Space, |remainderKernel e he g hg hs P q r| ≤ C*omega q*omega r) ∧
    (∀ q r : GW.Space, |remainderKernel e he g hg hs P q r-remainderKernel e he g hg hs 0 q r| ≤
      C*‖P‖*omega q*omega r) ∧
    ∀ q r : GW.Space,
      ‖fderiv ℝ (fun p => remainderKernel e he g hg hs P p r) q‖+
        ‖fderiv ℝ (fderiv ℝ (fun p => remainderKernel e he g hg hs P p r)) q‖ ≤ C*omega r) ∧
  ∀ P : GW.Space, kernelPsi e he g hg hs P 0 = 0 ∧
    (∀ q : GW.Space, remainderKernel e he g hg hs P q 0 = 0) ∧
    ∀ r : GW.Space, remainderKernel e he g hg hs P 0 r = 0

theorem finalKE02_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2), KE02FixedReference C e he g hg hs := by
  obtain ⟨A,hA,hAB⟩ := kernelConstant_quadratic_uniform
  obtain ⟨B,hB,hBB⟩ := kernelPsi_uniform_bound
  obtain ⟨F,hF,hFB⟩ := remainderKernel_uniform_bound
  obtain ⟨D,hD,hDB⟩ := remainderKernel_qDerivatives_uniform
  obtain ⟨T,hT,hTB⟩ := kernelMomentumDifferences_uniform
  let C := A+B+F+D+T+1
  have hC : 0 < C := by dsimp [C]; positivity
  have hAC : A ≤ C := by dsimp [C]; linarith
  have hBC : B ≤ C := by dsimp [C]; linarith
  have hFC : F ≤ C := by dsimp [C]; linarith
  have hDC : D ≤ C := by dsimp [C]; linarith
  have hTC : T ≤ C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro e he g hg hs
  constructor
  · intro P hP
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · exact (hAB e he g hg hs P hP).trans (mul_le_mul_of_nonneg_right hAC (sq_nonneg _))
    · intro q
      exact (hBB e he g hg hs P q hP).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBC (omega_nonneg q))
          (add_nonneg (omega_nonneg q) (norm_nonneg P)))
    · intro q
      exact ((hTB e he g hg hs P hP).1 q).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hTC (norm_nonneg P)) (omega_nonneg q))
    · intro q r
      exact (hFB e he g hg hs P q r hP).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hFC (omega_nonneg q)) (omega_nonneg r))
    · intro q r
      exact ((hTB e he g hg hs P hP).2 q r).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hTC (norm_nonneg P)) (omega_nonneg q)) (omega_nonneg r))
    · intro q r
      exact (hDB e he g hg hs P q r hP).trans (mul_le_mul_of_nonneg_right hDC (omega_nonneg r))
  · intro P
    exact ⟨kernelPsi_zero e he g hg hs P,remainderKernel_right_zero e he g hg hs P,
      remainderKernel_left_zero e he g hg hs P⟩

theorem finalKE02 : ∃ C s : ℝ, 0 < C ∧ 0 < s ∧ ∀ g : ℝ, |g| < s →
    ∃ he : groundEnergy (fiberHamiltonian g 0) ∈ Set.Icc (-1/4 : ℝ) 0,
    ∃ hg : |g| ≤ 1, ∃ hs : auxiliaryResolventConstant*|g| ≤ 1/2,
      KE02FixedReference C (groundEnergy (fiberHamiltonian g 0)) he g hg hs := by
  obtain ⟨C,hC,hB⟩ := finalKE02_uniform
  obtain ⟨s,hs,hGround⟩ := auxiliarySelfEnergy_zero_groundEnergy
  refine ⟨C,s,hC,hs,?_⟩
  intro g hgSmall
  obtain ⟨he,hg,hsmall,_⟩ := hGround g hgSmall
  exact ⟨he,hg,hsmall,hB _ he g hg hsmall⟩

end Froehlich
