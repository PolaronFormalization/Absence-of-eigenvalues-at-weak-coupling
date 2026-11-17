import Froehlich.Nodes.KE01KernelSymmetry
import Froehlich.Nodes.KE01KernelReflection

set_option autoImplicit false
noncomputable section
namespace Froehlich
variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2)

theorem remainderKernel_right_zero (P q : GW.Space) : remainderKernel e he g hg hs P q 0 = 0 := by
  unfold remainderKernel kernelPsi kernelConstant
  ring

theorem remainderKernel_symmetric (P q r : GW.Space) :
    remainderKernel e he g hg hs P q r = remainderKernel e he g hg hs P r q := by
  unfold remainderKernel
  rw [thresholdKernelC_symmetric e he g hg hs P q r]
  ring

theorem remainderKernel_left_zero (P r : GW.Space) : remainderKernel e he g hg hs P 0 r = 0 := by
  rw [remainderKernel_symmetric,remainderKernel_right_zero]

theorem kernelPsi_zeroMomentum_even : Function.Even (kernelPsi e he g hg hs 0) := by
  intro q
  have h := kernelPsi_reflection e he g hg hs 0 q
  simpa only [neg_zero] using h

theorem remainderKernel_reflection (P q r : GW.Space) :
    remainderKernel e he g hg hs (-P) (-q) (-r) = remainderKernel e he g hg hs P q r := by
  unfold remainderKernel
  rw [thresholdKernelC_reflection,kernelConstant_even,kernelPsi_reflection,kernelPsi_reflection]

/-- The remainder is the literal double difference in the two vector slots. -/
theorem remainderKernel_double_difference (P q r : GW.Space) :
    remainderKernel e he g hg hs P q r =
      (thresholdKernelC e he g hg hs P q r).re-(thresholdKernelC e he g hg hs P q 0).re-
        (thresholdKernelC e he g hg hs P 0 r).re+(thresholdKernelC e he g hg hs P 0 0).re := by
  unfold remainderKernel kernelPsi kernelConstant
  rw [thresholdKernelC_symmetric e he g hg hs P 0 r]
  ring

end Froehlich
