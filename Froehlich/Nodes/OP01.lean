import Froehlich.Nodes.OP01Inverse

set_option autoImplicit false

/-! OP01 / lem:boundedkernel, on the actual GW one-particle L2 space.
The integral operator, source vector and m+g²K operator have their literal
AE actions. All quantitative constants and the cutoff precede signed g. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

def OP01OperatorsReference (C CD e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (hCD : 0 ≤ CD)
    (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2)
    (P : GW.Space) (hP : ‖P‖ ≤ 1/4) : Prop :=
  ‖thresholdIntegralOperator e he g hg hs P hP‖ ≤ C ∧
  ‖thresholdKernelSourceVector e he g hg hs P hP‖ ≤ C*|g| ∧
  (∀ f : GW.OnePhonon, thresholdIntegralOperator e he g hg hs P hP f =ᵐ[volume]
    (fun q => ∫ r, boundedThresholdKernel e he g hg hs P q r*f r)) ∧
  (thresholdKernelSourceVector e he g hg hs P hP =ᵐ[volume] kernelSourceCoefficient e he g hg hs P) ∧
  (thresholdIntegralOperator e he g hg hs P hP).adjoint = thresholdIntegralOperator e he g hg hs P hP ∧
  (∀ f : GW.OnePhonon, thresholdIntegralOperator e he g hg hs P hP (conjugateOnePhonon f) =
    conjugateOnePhonon (thresholdIntegralOperator e he g hg hs P hP f)) ∧
  conjugateOnePhonon (thresholdKernelSourceVector e he g hg hs P hP) = thresholdKernelSourceVector e he g hg hs P hP ∧
  (thresholdBoundedOperator e he g hg hs CD hCD hquad P hP).adjoint = thresholdBoundedOperator e he g hg hs CD hCD hquad P hP ∧
  (∀ f : GW.OnePhonon, thresholdBoundedOperator e he g hg hs CD hCD hquad P hP (conjugateOnePhonon f) =
    conjugateOnePhonon (thresholdBoundedOperator e he g hg hs CD hCD hquad P hP f)) ∧
  (∀ f : GW.OnePhonon, thresholdBoundedOperator e he g hg hs CD hCD hquad P hP f =ᵐ[volume]
    (fun q => (thresholdDiagonalMultiplier e he g hg hs q : ℂ)*f q+
      ((g^2 : ℝ) : ℂ)*(∫ r, boundedThresholdKernel e he g hg hs P q r*f r))) ∧
  ‖thresholdBoundedOperator e he g hg hs CD hCD hquad P hP-1‖ ≤ C*g^2 ∧
  (∀ f : GW.OnePhonon, ‖f‖^2/2 ≤ (⟪f,thresholdBoundedOperator e he g hg hs CD hCD hquad P hP f⟫_ℂ).re) ∧
  thresholdBoundedInverse e he g hg hs CD hCD hquad P hP * thresholdBoundedOperator e he g hg hs CD hCD hquad P hP = 1 ∧
  thresholdBoundedOperator e he g hg hs CD hCD hquad P hP * thresholdBoundedInverse e he g hg hs CD hCD hquad P hP = 1 ∧
  ‖thresholdBoundedInverse e he g hg hs CD hCD hquad P hP‖ ≤ 2 ∧
  (thresholdBoundedInverse e he g hg hs CD hCD hquad P hP).adjoint = thresholdBoundedInverse e he g hg hs CD hCD hquad P hP ∧
  ∀ f : GW.OnePhonon, thresholdBoundedInverse e he g hg hs CD hCD hquad P hP (conjugateOnePhonon f) =
    conjugateOnePhonon (thresholdBoundedInverse e he g hg hs CD hCD hquad P hP f)

def OP01FixedReference (C CD e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (hCD : 0 ≤ CD)
    (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2) : Prop :=
  thresholdDiagonalMultiplier e he g hg hs 0 = 1 ∧
  Measurable (thresholdDiagonalMultiplier e he g hg hs) ∧
  Function.Even (thresholdDiagonalMultiplier e he g hg hs) ∧
  (∀ q : GW.Space, |thresholdDiagonalMultiplier e he g hg hs q-1| ≤ C*g^2) ∧
  (∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier e he g hg hs q) ∧
  ∀ (P : GW.Space) (hP : ‖P‖ ≤ 1/4), OP01OperatorsReference C CD e he g hg hs hCD hquad P hP

theorem finalOP01 : ∃ C CD s : ℝ, 0 < C ∧ 0 < CD ∧ 0 < s ∧
    ∀ g : ℝ, |g| < s →
      ∃ he : groundEnergy (fiberHamiltonian g 0) ∈ Set.Icc (-1/4 : ℝ) 0,
      ∃ hg : |g| ≤ 1, ∃ hs : auxiliaryResolventConstant*|g| ≤ 1/2,
      ∃ hCD : 0 ≤ CD,
      ∃ hquad : ∀ q : GW.Space,
        |auxiliarySelfEnergy (groundEnergy (fiberHamiltonian g 0)) q he g hg hs-groundEnergy (fiberHamiltonian g 0)| ≤
          CD*g^2*‖q‖^2,
      OP01FixedReference C CD (groundEnergy (fiberHamiltonian g 0)) he g hg hs hCD hquad := by
  obtain ⟨CK,hCK,hK⟩ := thresholdIntegralOperator_norm_uniform
  obtain ⟨CB,hCB,hB⟩ := thresholdKernelSourceVector_norm_uniform
  obtain ⟨CD,CT,s,hCD,hCT,hs,hGround⟩ := op01_ground_smallness
  let C := CK+CB+CT+CD+1
  have hC : 0 < C := by dsimp [C]; positivity
  have hKC : CK ≤ C := by dsimp [C]; linarith
  have hBC : CB ≤ C := by dsimp [C]; linarith
  have hTC : CT ≤ C := by dsimp [C]; linarith
  have hDCC : CD ≤ C := by dsimp [C]; linarith
  refine ⟨C,CD,s,hC,hCD,hs,?_⟩
  intro g hgs
  obtain ⟨he,hg,haux,hCD0,hquad,hControl,hM⟩ := hGround g hgs
  refine ⟨he,hg,haux,hCD0,hquad,thresholdDiagonalMultiplier_zero _ he g hg haux,?_,?_,?_,hM,?_⟩
  · exact thresholdDiagonalMultiplier_measurable _ he g hg haux
  · exact thresholdDiagonalMultiplier_even _ he g hg haux
  · intro q
    exact (thresholdDiagonalMultiplier_sub_one_bound _ he g hg haux CD hCD0 hquad q).trans
      (mul_le_mul_of_nonneg_right hDCC (sq_nonneg g))
  · intro P hP
    have hN := (hControl P hP).2
    have hI := thresholdBoundedInverse_spec _ he g hg haux CD hCD0 hquad P hP hN
    refine ⟨(hK _ he g hg haux P hP).trans hKC,
      (hB _ he g hg haux P hP).trans (mul_le_mul_of_nonneg_right hBC (abs_nonneg g)),
      thresholdIntegralOperator_ae _ he g hg haux P hP,thresholdKernelSourceVector_ae _ he g hg haux P hP,
      thresholdIntegralOperator_selfadjoint _ he g hg haux P hP,thresholdIntegralOperator_conjugation _ he g hg haux P hP,
      thresholdKernelSourceVector_real _ he g hg haux P hP,thresholdBoundedOperator_selfadjoint _ he g hg haux CD hCD0 hquad P hP,
      thresholdBoundedOperator_conjugation _ he g hg haux CD hCD0 hquad P hP,
      thresholdBoundedOperator_ae _ he g hg haux CD hCD0 hquad P hP,
      ((hControl P hP).1).trans (mul_le_mul_of_nonneg_right hTC (sq_nonneg g)),
      thresholdBoundedOperator_quadratic_lower _ he g hg haux CD hCD0 hquad P hP hN,
      hI.1,hI.2.1,hI.2.2,thresholdBoundedInverse_selfadjoint _ he g hg haux CD hCD0 hquad P hP hN,
      thresholdBoundedInverse_conjugation _ he g hg haux CD hCD0 hquad P hP hN⟩

end Froehlich
