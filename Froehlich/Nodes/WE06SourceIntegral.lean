import Froehlich.Nodes.WE05WeightedVector
import Froehlich.Nodes.WE01Kernel
import Froehlich.Nodes.WE01Source

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

private theorem we06_source_inner_scalar (g w psi eta mu : ℝ) (hmu : w^2 = mu) :
    ⟪(g : ℂ)*(w : ℂ)*(psi : ℂ),(g : ℂ)*(w : ℂ)*(eta : ℂ)⟫_ℂ =
      ((g^2*(psi*eta*mu) : ℝ) : ℂ) := by
  rw [←hmu]
  simp only [RCLike.inner_apply',map_mul,Complex.conj_ofReal,
    Complex.ofReal_mul,Complex.ofReal_pow]
  ring

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P : GW.Space) (hP : ‖P‖ ≤ 1/4)
    (eta : GW.Space → ℝ) (hEta : AEStronglyMeasurable eta volume) (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ᵐ q ∂volume, |eta q| ≤ M*omega q)

include hP hEta hM hBound in
theorem we06_source_product_integrable :
    Integrable (fun q : GW.Space => kernelPsi e he g hg hs P q*eta q*muDensity P q) volume := by
  obtain ⟨C,hC,hPsi⟩ := kernelPsi_uniform_bound
  have hm : AEStronglyMeasurable
      (fun q : GW.Space => kernelPsi e he g hg hs P q*eta q*muDensity P q) volume :=
    ((kernelPsi_measurable e he g hg hs P).aestronglyMeasurable.mul hEta).mul
      (muDensity_measurable P).aestronglyMeasurable
  apply ((weightedKernelDensity_integrable P hP).const_mul ((2*C)*M)).mono' hm
  filter_upwards [hBound] with q hq
  have hpsi : |kernelPsi e he g hg hs P q| ≤ (2*C)*omega q := by
    have hsum : omega q+‖P‖ ≤ 2 := by linarith [omega_le_one q]
    have h := (hPsi e he g hg hs P q hP).trans
      (mul_le_mul_of_nonneg_left hsum (mul_nonneg hC.le (omega_nonneg q)))
    simpa only [mul_assoc,mul_comm,mul_left_comm] using h
  have h := mul_le_mul hpsi hq (abs_nonneg (eta q)) (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC.le) (omega_nonneg q))
  have h' := mul_le_mul_of_nonneg_right h (muDensity_nonneg P q)
  simpa only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (muDensity_nonneg P q),
    weightedKernelDensity,pow_two,mul_assoc,mul_comm,mul_left_comm] using h'

include hM in
/-- Literal absolutely convergent N integral, before actual inverse identification. -/
theorem weightedHilbertVector_source_inner_integral :
    ⟪thresholdKernelSourceVector e he g hg hs P hP,
      weightedHilbertVector g P hP eta hEta M hBound⟫_ℂ =
      ((g^2*(∫ q : GW.Space,kernelPsi e he g hg hs P q*eta q*muDensity P q) : ℝ) : ℂ) := by
  rw [L2.inner_def]
  calc
    _ = ∫ q : GW.Space,((g^2*(kernelPsi e he g hg hs P q*eta q*muDensity P q) : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [thresholdKernelSourceVector_ae e he g hg hs P hP,
        weightedHilbertVector_ae g P hP eta hEta M hBound] with q hb hx
      rw [hb,hx]
      exact we06_source_inner_scalar g (wDensity P q) (kernelPsi e he g hg hs P q)
        (eta q) (muDensity P q) (wDensity_sq P q)
    _ = _ := by rw [integral_complex_ofReal,integral_const_mul]

end Froehlich
