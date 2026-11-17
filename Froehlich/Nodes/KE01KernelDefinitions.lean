import Froehlich.Nodes.KE01KernelReality

set_option autoImplicit false
noncomputable section
namespace Froehlich
variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant * |g| ≤ 1/2)

/-- The scalar kernel coefficient, distinct from the vacuum Schur scalar. -/
def kernelConstant (P : GW.Space) : ℝ := (thresholdKernelC e he g hg hs P 0 0).re

def kernelPsi (P q : GW.Space) : ℝ :=
  (thresholdKernelC e he g hg hs P q 0).re-kernelConstant e he g hg hs P

def remainderKernel (P q r : GW.Space) : ℝ :=
  (thresholdKernelC e he g hg hs P q r).re-kernelConstant e he g hg hs P-
    kernelPsi e he g hg hs P q-kernelPsi e he g hg hs P r

theorem kernelConstant_ofReal (P : GW.Space) :
    (kernelConstant e he g hg hs P : ℂ) = thresholdKernelC e he g hg hs P 0 0 :=
  thresholdKernelC_ofReal_re e he g hg hs P 0 0

theorem kernelPsi_ofReal (P q : GW.Space) :
    (kernelPsi e he g hg hs P q : ℂ) =
      thresholdKernelC e he g hg hs P q 0-(kernelConstant e he g hg hs P : ℂ) := by
  unfold kernelPsi
  rw [Complex.ofReal_sub,thresholdKernelC_ofReal_re]

theorem remainderKernel_ofReal (P q r : GW.Space) :
    (remainderKernel e he g hg hs P q r : ℂ) =
      thresholdKernelC e he g hg hs P q r-(kernelConstant e he g hg hs P : ℂ)-
        (kernelPsi e he g hg hs P q : ℂ)-(kernelPsi e he g hg hs P r : ℂ) := by
  unfold remainderKernel
  simp only [Complex.ofReal_sub,thresholdKernelC_ofReal_re]

theorem thresholdKernelC_decomposition (P q r : GW.Space) :
    thresholdKernelC e he g hg hs P q r =
      ((kernelConstant e he g hg hs P+kernelPsi e he g hg hs P q+
        kernelPsi e he g hg hs P r+remainderKernel e he g hg hs P q r : ℝ) : ℂ) := by
  rw [Complex.ofReal_add,Complex.ofReal_add,Complex.ofReal_add,remainderKernel_ofReal]
  ring

theorem kernelPsi_zero (P : GW.Space) : kernelPsi e he g hg hs P 0 = 0 := by
  exact sub_self _

end Froehlich
