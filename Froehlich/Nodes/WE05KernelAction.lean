import Froehlich.Nodes.WE05WeightedVector
import Froehlich.Nodes.WE01EtaIntegral

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace Froehlich

private theorem we05_kernel_scalar (a b F g v mu : ℝ) (hb : b^2 = mu) :
    (a : ℂ)*(F : ℂ)*(b : ℂ)*((g : ℂ)*(b : ℂ)*(v : ℂ)) =
      (g : ℂ)*(a : ℂ)*((F*mu*v : ℝ) : ℂ) := by
  rw [←hb,Complex.ofReal_mul,Complex.ofReal_mul,Complex.ofReal_pow]
  ring

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P : GW.Space) (hP : ‖P‖ ≤ 1/4)
    (eta : GW.Space → ℝ) (hEta : AEStronglyMeasurable eta volume) (M : ℝ)
    (hM : 0 ≤ M) (hBound : ∀ᵐ r ∂volume, |eta r| ≤ M*omega r)

/-- The single-row substitution uses the exact identity w squared equals mu. -/
theorem weightedHilbertCoefficient_kernel_row (q r : GW.Space) :
    boundedThresholdKernel e he g hg hs P q r*weightedHilbertCoefficient g P eta r =
      (g : ℂ)*(wDensity P q : ℂ)*
        ((remainderKernel e he g hg hs P q r*muDensity P r*eta r : ℝ) : ℂ) :=
  we05_kernel_scalar (wDensity P q) (wDensity P r)
    (remainderKernel e he g hg hs P q r) g (eta r) (muDensity P r) (wDensity_sq P r)

include hM in
/-- Both rows are absolutely integrable; the identity uses one integral only. -/
theorem weightedHilbertVector_kernel_row (q : GW.Space) :
    Integrable (fun r => boundedThresholdKernel e he g hg hs P q r*
      weightedHilbertVector g P hP eta hEta M hBound r) volume ∧
    Integrable (fun r => remainderKernel e he g hg hs P q r*muDensity P r*eta r) volume ∧
    (∫ r, boundedThresholdKernel e he g hg hs P q r*
      weightedHilbertVector g P hP eta hEta M hBound r) =
        (g : ℂ)*(wDensity P q : ℂ)*(weightedEtaIntegral e he g hg hs P eta q : ℂ) := by
  let x := weightedHilbertVector g P hP eta hEta M hBound
  have hk := kernelRow_integrable (kernelDensityMajorant P) (kernelDensityMajorant_memLp P hP)
    (boundedThresholdKernel e he g hg hs P) (boundedThresholdKernel_measurable e he g hg hs P)
    integralKernelMajorantConstant (integralKernelMajorantConstant_bound e he g hg hs P hP) x q
  obtain ⟨CI,hCI,hI⟩ := weightedEtaIntegral_uniform
  have hi := (hI e he g hg hs P hP M hM eta hEta hBound q).1
  refine ⟨hk,hi,?_⟩
  calc
    _ = ∫ r, (g : ℂ)*(wDensity P q : ℂ)*
        ((remainderKernel e he g hg hs P q r*muDensity P r*eta r : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [weightedHilbertVector_ae g P hP eta hEta M hBound] with r hr
      rw [hr]
      exact weightedHilbertCoefficient_kernel_row e he g hg hs P eta q r
    _ = (g : ℂ)*(wDensity P q : ℂ)*(weightedEtaIntegral e he g hg hs P eta q : ℂ) := by
      rw [integral_const_mul,integral_complex_ofReal]
      rfl

include hM in
theorem weightedHilbertVector_integralOperator_ae :
    thresholdIntegralOperator e he g hg hs P hP (weightedHilbertVector g P hP eta hEta M hBound)
      =ᵐ[volume] (fun q => (g : ℂ)*(wDensity P q : ℂ)*
        (weightedEtaIntegral e he g hg hs P eta q : ℂ)) := by
  filter_upwards [thresholdIntegralOperator_ae e he g hg hs P hP
    (weightedHilbertVector g P hP eta hEta M hBound)] with q hq
  exact hq.trans (weightedHilbertVector_kernel_row e he g hg hs P hP eta hEta M hM hBound q).2.2

end Froehlich
