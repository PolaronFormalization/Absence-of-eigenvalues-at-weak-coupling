import Froehlich.Nodes.OP01MajorantL2

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace Froehlich

def integralKernelMajorantConstant : ℝ := boundedThresholdKernel_product_majorant.choose

theorem integralKernelMajorantConstant_positive : 0 < integralKernelMajorantConstant :=
  boundedThresholdKernel_product_majorant.choose_spec.1

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P : GW.Space) (hP : ‖P‖ ≤ 1/4)

include hP in
theorem integralKernelMajorantConstant_bound (q r : GW.Space) :
    ‖boundedThresholdKernel e he g hg hs P q r‖ ≤
      integralKernelMajorantConstant*kernelDensityMajorant P q*kernelDensityMajorant P r :=
  boundedThresholdKernel_product_majorant.choose_spec.2 e he g hg hs P q r hP

def thresholdIntegralOperator : GW.OnePhonon →L[ℂ] GW.OnePhonon :=
  kernelIntegralOperator (kernelDensityMajorant P) (kernelDensityMajorant_memLp P hP)
    (kernelDensityMajorant_nonnegative P) (boundedThresholdKernel e he g hg hs P)
    (boundedThresholdKernel_measurable e he g hg hs P) integralKernelMajorantConstant
    integralKernelMajorantConstant_positive.le (integralKernelMajorantConstant_bound e he g hg hs P hP)

theorem thresholdIntegralOperator_ae (f : GW.OnePhonon) :
    thresholdIntegralOperator e he g hg hs P hP f =ᵐ[volume]
      (fun q => ∫ r, boundedThresholdKernel e he g hg hs P q r*f r) :=
  kernelIntegralOperator_ae (kernelDensityMajorant P) (kernelDensityMajorant_memLp P hP)
    (kernelDensityMajorant_nonnegative P) (boundedThresholdKernel e he g hg hs P)
    (boundedThresholdKernel_measurable e he g hg hs P) integralKernelMajorantConstant
    integralKernelMajorantConstant_positive.le (integralKernelMajorantConstant_bound e he g hg hs P hP) f

include hP in
theorem kernelSourceCoefficient_memLp : MemLp (kernelSourceCoefficient e he g hg hs P) 2 volume := by
  obtain ⟨C,hC,hB⟩ := kernelSourceCoefficient_majorant
  apply ((kernelDensityMajorant_memLp P hP).const_mul (C*|g|)).mono'
    (kernelSourceCoefficient_measurable e he g hg hs P).aestronglyMeasurable
  exact Eventually.of_forall (fun q => hB e he g hg hs P q hP)

def thresholdKernelSourceVector : GW.OnePhonon :=
  (kernelSourceCoefficient_memLp e he g hg hs P hP).toLp (kernelSourceCoefficient e he g hg hs P)

theorem thresholdKernelSourceVector_ae : thresholdKernelSourceVector e he g hg hs P hP =ᵐ[volume]
    kernelSourceCoefficient e he g hg hs P := MemLp.coeFn_toLp _

theorem thresholdIntegralOperator_norm_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P : GW.Space) (hP : ‖P‖ ≤ 1/4),
      ‖thresholdIntegralOperator e he g hg hs P hP‖ ≤ C := by
  obtain ⟨CI,hCI,hB⟩ := kernelDensityMajorant_squaredNorm_uniform
  refine ⟨integralKernelMajorantConstant*CI,mul_pos integralKernelMajorantConstant_positive hCI,?_⟩
  intro e he g hg hs P hP
  exact (kernelIntegralOperator_norm_le (kernelDensityMajorant P) (kernelDensityMajorant_memLp P hP)
    (kernelDensityMajorant_nonnegative P) (boundedThresholdKernel e he g hg hs P)
    (boundedThresholdKernel_measurable e he g hg hs P) integralKernelMajorantConstant
    integralKernelMajorantConstant_positive.le (integralKernelMajorantConstant_bound e he g hg hs P hP)).trans
      (mul_le_mul_of_nonneg_left (hB P hP) integralKernelMajorantConstant_positive.le)

theorem thresholdKernelSourceVector_norm_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P : GW.Space) (hP : ‖P‖ ≤ 1/4),
      ‖thresholdKernelSourceVector e he g hg hs P hP‖ ≤ C*|g| := by
  obtain ⟨CB,hCB,hB⟩ := kernelSourceCoefficient_majorant
  obtain ⟨CI,hCI,hI⟩ := kernelDensityMajorant_squaredNorm_uniform
  refine ⟨CB*(CI+1),by positivity,?_⟩
  intro e he g hg hs P hP
  let a := (kernelDensityMajorant_memLp P hP).toLp (kernelDensityMajorant P)
  have ha : ‖a‖ ≤ CI+1 := by
    have hi := hI P hP
    have hn := norm_nonneg a
    change ‖a‖^2 ≤ CI at hi
    nlinarith
  have hb : ‖thresholdKernelSourceVector e he g hg hs P hP‖ ≤ (CB*|g|)*‖a‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [thresholdKernelSourceVector_ae e he g hg hs P hP,
      MemLp.coeFn_toLp (kernelDensityMajorant_memLp P hP)] with q hq haq
    rw [hq,haq,Real.norm_eq_abs,abs_of_nonneg (kernelDensityMajorant_nonnegative P q)]
    exact hB e he g hg hs P q hP
  exact hb.trans ((mul_le_mul_of_nonneg_left ha (mul_nonneg hCB.le (abs_nonneg g))).trans_eq (by ring))

end Froehlich
