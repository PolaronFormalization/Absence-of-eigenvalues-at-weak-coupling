import Froehlich.Nodes.WE05KernelAction
import Froehlich.Nodes.OP01Inverse

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace Froehlich

private theorem we05_scalar_equation (m v g w I psi : ℝ) (h : m*v+g^2*I = psi) :
    (m : ℂ)*((g : ℂ)*(w : ℂ)*(v : ℂ))+
      ((g^2 : ℝ) : ℂ)*((g : ℂ)*(w : ℂ)*(I : ℂ)) =
        (g : ℂ)*(w : ℂ)*(psi : ℂ) := by
  have hc : (m : ℂ)*(v : ℂ)+(g : ℂ)^2*(I : ℂ) = (psi : ℂ) := by
    simpa only [Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_pow] using
      congrArg (fun a : ℝ => (a : ℂ)) h
  calc
    _ = (g : ℂ)*(w : ℂ)*((m : ℂ)*(v : ℂ)+(g : ℂ)^2*(I : ℂ)) := by
      rw [Complex.ofReal_pow]
      ring
    _ = _ := congrArg (fun a : ℂ => (g : ℂ)*(w : ℂ)*a) hc

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (CD : ℝ) (hCD : 0 ≤ CD)
    (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2)
    (P : GW.Space) (hP : ‖P‖ ≤ 1/4) (eta : GW.Space → ℝ)
    (hEta : AEStronglyMeasurable eta volume) (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ᵐ q ∂volume, |eta q| ≤ M*omega q)
    (hEquation : ∀ᵐ q ∂volume,
      thresholdDiagonalMultiplier e he g hg hs q*eta q+
        g^2*weightedEtaIntegral e he g hg hs P eta q = kernelPsi e he g hg hs P q)

include hM hEquation in
/-- Multiplication of the actual weighted equation yields the actual Bx=b. -/
theorem weightedHilbertVector_boundedOperator :
    thresholdBoundedOperator e he g hg hs CD hCD hquad P hP
      (weightedHilbertVector g P hP eta hEta M hBound) =
        thresholdKernelSourceVector e he g hg hs P hP := by
  apply Lp.ext
  filter_upwards [thresholdBoundedOperator_ae e he g hg hs CD hCD hquad P hP
      (weightedHilbertVector g P hP eta hEta M hBound),
    weightedHilbertVector_ae g P hP eta hEta M hBound,
    thresholdKernelSourceVector_ae e he g hg hs P hP,hEquation] with q hb hx hsource hq
  rw [hb,hx,(weightedHilbertVector_kernel_row e he g hg hs P hP eta hEta M hM hBound q).2.2,hsource]
  exact we05_scalar_equation (thresholdDiagonalMultiplier e he g hg hs q) (eta q) g (wDensity P q)
    (weightedEtaIntegral e he g hg hs P eta q) (kernelPsi e he g hg hs P q) hq

include hM hEquation in
theorem weightedHilbertVector_eq_inverse
    (hN : ‖thresholdBoundedOperator e he g hg hs CD hCD hquad P hP-1‖ ≤ 1/2) :
    weightedHilbertVector g P hP eta hEta M hBound =
      thresholdBoundedInverse e he g hg hs CD hCD hquad P hP
        (thresholdKernelSourceVector e he g hg hs P hP) := by
  let x := weightedHilbertVector g P hP eta hEta M hBound
  let B := thresholdBoundedOperator e he g hg hs CD hCD hquad P hP
  let R := thresholdBoundedInverse e he g hg hs CD hCD hquad P hP
  have hleft := (thresholdBoundedInverse_spec e he g hg hs CD hCD hquad P hP hN).1
  have h := congrArg (fun T : GW.OnePhonon →L[ℂ] GW.OnePhonon => T x) hleft
  have hRx : R (B x) = x := by
    simpa only [mul_apply_eq_comp,one_apply_eq_self] using h
  have hBx := weightedHilbertVector_boundedOperator e he g hg hs CD hCD hquad P hP
    eta hEta M hM hBound hEquation
  rw [hBx] at hRx
  exact hRx.symm

end Froehlich
