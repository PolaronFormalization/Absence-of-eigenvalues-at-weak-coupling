import Froehlich.Nodes.OP01KernelConstruction

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace Froehlich
variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P : GW.Space) (hP : ‖P‖ ≤ 1/4)

theorem boundedThresholdKernel_hermitian (q r : GW.Space) :
    boundedThresholdKernel e he g hg hs P q r =
      (starRingEnd ℂ) (boundedThresholdKernel e he g hg hs P r q) := by
  simp only [boundedThresholdKernel,map_mul,Complex.conj_ofReal]
  rw [remainderKernel_symmetric e he g hg hs P r q]
  ring

theorem boundedThresholdKernel_real (q r : GW.Space) :
    (starRingEnd ℂ) (boundedThresholdKernel e he g hg hs P q r) =
      boundedThresholdKernel e he g hg hs P q r := by
  simp only [boundedThresholdKernel,map_mul,Complex.conj_ofReal]

theorem kernelSourceCoefficient_real (q : GW.Space) :
    (starRingEnd ℂ) (kernelSourceCoefficient e he g hg hs P q) =
      kernelSourceCoefficient e he g hg hs P q := by
  simp only [kernelSourceCoefficient,map_mul,Complex.conj_ofReal]

theorem thresholdIntegralOperator_selfadjoint :
    (thresholdIntegralOperator e he g hg hs P hP).adjoint = thresholdIntegralOperator e he g hg hs P hP := by
  exact kernelIntegralOperator_adjoint (kernelDensityMajorant P) (kernelDensityMajorant_memLp P hP)
    (kernelDensityMajorant_nonnegative P) (boundedThresholdKernel e he g hg hs P)
    (boundedThresholdKernel_measurable e he g hg hs P) integralKernelMajorantConstant
    integralKernelMajorantConstant_positive.le (integralKernelMajorantConstant_bound e he g hg hs P hP)
    (Eventually.of_forall (fun z => boundedThresholdKernel_hermitian e he g hg hs P z.1 z.2))

theorem thresholdIntegralOperator_conjugation (f : GW.OnePhonon) :
    thresholdIntegralOperator e he g hg hs P hP (conjugateOnePhonon f) =
      conjugateOnePhonon (thresholdIntegralOperator e he g hg hs P hP f) := by
  exact kernelIntegralOperator_conjugation (kernelDensityMajorant P) (kernelDensityMajorant_memLp P hP)
    (kernelDensityMajorant_nonnegative P) (boundedThresholdKernel e he g hg hs P)
    (boundedThresholdKernel_measurable e he g hg hs P) integralKernelMajorantConstant
    integralKernelMajorantConstant_positive.le (integralKernelMajorantConstant_bound e he g hg hs P hP)
    (Eventually.of_forall (fun z => boundedThresholdKernel_real e he g hg hs P z.1 z.2)) f

theorem thresholdKernelSourceVector_real :
    conjugateOnePhonon (thresholdKernelSourceVector e he g hg hs P hP) =
      thresholdKernelSourceVector e he g hg hs P hP := by
  apply Lp.ext
  filter_upwards [conjugateOnePhonon_ae (thresholdKernelSourceVector e he g hg hs P hP),
    thresholdKernelSourceVector_ae e he g hg hs P hP] with q hc hq
  rw [hc,hq,kernelSourceCoefficient_real]

end Froehlich
