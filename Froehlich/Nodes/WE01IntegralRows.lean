import Froehlich.Nodes.WE01Kernel
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace Froehlich

/-- Native L-infinity representatives satisfy their essential norm bound. -/
theorem linftyReal_ae_norm_le (f : Lp ℝ ⊤ (volume : Measure GW.Space)) :
    ∀ᵐ r ∂volume, ‖f r‖ ≤ ‖f‖ :=
  ae_le_lpNorm_exponent_top (Lp.memLp f)

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P : GW.Space) (hP : ‖P‖ ≤ 1/4)
    (C : ℝ) (hC : 0 ≤ C)
    (hK : ∀ q r, ‖normalizedWeightedKernel e he g hg hs P q r‖ ≤ C*weightedKernelDensity P r)

/-- The actual integral on ordinary real L-infinity representatives. -/
def normalizedWeightedIntegral (f : Lp ℝ ⊤ (volume : Measure GW.Space)) (q : GW.Space) : ℝ :=
  ∫ r, normalizedWeightedKernel e he g hg hs P q r*f r

include hC hK in
theorem normalizedWeightedIntegral_integrand_bound (f : Lp ℝ ⊤ (volume : Measure GW.Space))
    (q : GW.Space) :
    ∀ᵐ r ∂volume, ‖normalizedWeightedKernel e he g hg hs P q r*f r‖ ≤
      (C*‖f‖)*weightedKernelDensity P r := by
  filter_upwards [linftyReal_ae_norm_le f] with r hr
  rw [norm_mul]
  have h := mul_le_mul (hK q r) hr (norm_nonneg _) (mul_nonneg hC (weightedKernelDensity_nonnegative P r))
  simpa only [mul_assoc,mul_comm,mul_left_comm] using h

include hP hC hK in
theorem normalizedWeightedIntegral_integrable (f : Lp ℝ ⊤ (volume : Measure GW.Space))
    (q : GW.Space) :
    Integrable (fun r => normalizedWeightedKernel e he g hg hs P q r*f r) volume := by
  have hm : Measurable (fun r => normalizedWeightedKernel e he g hg hs P q r) :=
    (normalizedWeightedKernel_measurable e he g hg hs P).comp
      (measurable_const.prodMk measurable_id)
  exact ((weightedKernelDensity_integrable P hP).const_mul (C*‖f‖)).mono'
    (hm.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    (normalizedWeightedIntegral_integrand_bound e he g hg hs P C hC hK f q)

theorem normalizedWeightedIntegral_aestronglyMeasurable
    (f : Lp ℝ ⊤ (volume : Measure GW.Space)) :
    AEStronglyMeasurable (normalizedWeightedIntegral e he g hg hs P f) volume := by
  have hm : AEStronglyMeasurable
      (fun qr : GW.Space × GW.Space => normalizedWeightedKernel e he g hg hs P qr.1 qr.2*f qr.2)
      (volume.prod volume) :=
    (normalizedWeightedKernel_measurable e he g hg hs P).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable f).comp_snd
  exact hm.integral_prod_right'

include hP hC hK in
theorem normalizedWeightedIntegral_norm_le (f : Lp ℝ ⊤ (volume : Measure GW.Space))
    (q : GW.Space) :
    ‖normalizedWeightedIntegral e he g hg hs P f q‖ ≤
      (C*(∫ r, weightedKernelDensity P r))*‖f‖ := by
  have h := norm_integral_le_of_norm_le
    ((weightedKernelDensity_integrable P hP).const_mul (C*‖f‖))
    (normalizedWeightedIntegral_integrand_bound e he g hg hs P C hC hK f q)
  simpa only [normalizedWeightedIntegral,integral_const_mul,integral_mul_const,mul_assoc,mul_comm,mul_left_comm] using h

/-- Integrating against this density respects any AE change of input representative. -/
theorem normalizedWeightedIntegral_congr_ae (f : Lp ℝ ⊤ (volume : Measure GW.Space))
    (z : GW.Space → ℝ) (hz : z =ᵐ[volume] f) (q : GW.Space) :
    (∫ r, normalizedWeightedKernel e he g hg hs P q r*z r) =
      normalizedWeightedIntegral e he g hg hs P f q := by
  apply integral_congr_ae
  filter_upwards [hz] with r hr
  rw [hr]

end Froehlich
