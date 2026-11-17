import Froehlich.Nodes.WE06Scalars

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

private theorem we06_hilbert_inner_scalar (g w eta mu : ℝ) (hmu : w^2 = mu) :
    ⟪(g : ℂ)*(w : ℂ)*(eta : ℂ),(g : ℂ)*(w : ℂ)⟫_ℂ =
      ((g^2*(eta*mu) : ℝ) : ℂ) := by
  rw [←hmu]
  simp only [RCLike.inner_apply',map_mul,Complex.conj_ofReal,
    Complex.ofReal_mul,Complex.ofReal_pow]
  ring

variable (g : ℝ) (P : GW.Space) (hP : ‖P‖ ≤ 1/4) (hP0 : P ≠ 0)
    (eta : GW.Space → ℝ) (hEta : AEStronglyMeasurable eta volume) (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ᵐ q ∂volume, |eta q| ≤ M*omega q)

include hEta hP0 hM hBound in
/-- The raw U integrand is absolutely integrable at nonzero momentum, also when g=0. -/
theorem we06_eta_mu_integrable : Integrable (fun q : GW.Space => eta q*muDensity P q) volume := by
  have hm : AEStronglyMeasurable (fun q : GW.Space => eta q*muDensity P q) volume :=
    hEta.mul (muDensity_measurable P).aestronglyMeasurable
  apply ((muDensity_integrable_bound P hP0).1.const_mul M).mono' hm
  filter_upwards [hBound] with q hq
  have he : |eta q| ≤ M := hq.trans (by simpa only [mul_one] using (mul_le_mul_of_nonneg_left (omega_le_one q) hM))
  have h := mul_le_mul_of_nonneg_right he (muDensity_nonneg P q)
  simpa only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (muDensity_nonneg P q)] using h

include hM in
/-- The genuine complex Hilbert pairing is the real absolutely convergent U integral. -/
theorem weightedHilbertVector_hilbertSource_inner_integral :
    ⟪weightedHilbertVector g P hP eta hEta M hBound,translatedHilbertSource g P hP0⟫_ℂ =
      ((g^2*(∫ q : GW.Space,eta q*muDensity P q) : ℝ) : ℂ) := by
  rw [L2.inner_def]
  calc
    _ = ∫ q : GW.Space,((g^2*(eta q*muDensity P q) : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [weightedHilbertVector_ae g P hP eta hEta M hBound,
        translatedHilbertSource_ae g P hP0] with q hx ht
      rw [hx,ht]
      exact we06_hilbert_inner_scalar g (wDensity P q) (eta q) (muDensity P q) (wDensity_sq P q)
    _ = _ := by rw [integral_complex_ofReal,integral_const_mul]

end Froehlich
