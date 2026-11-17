import Froehlich.Nodes.AN01
import Froehlich.Nodes.SE03InverseAlgebra

set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace Froehlich

/-- AN01 forces the coefficient of the actual infrared row to vanish. -/
theorem se03_infrared_coefficient_eq_zero (g : ℝ) (hg : g ≠ 0)
    (d : GW.OnePhonon) (a : ℂ)
    (hidentity : d =ᵐ[volume] (fun q : GW.Space => ((g/‖q‖^2 : ℝ) : ℂ)*a)) :
    a = 0 := by
  by_contra ha
  let v : GW.OnePhonon := (a*(g : ℂ))⁻¹ • d
  have hc : a*(g : ℂ) ≠ 0 := mul_ne_zero ha (Complex.ofReal_ne_zero.mpr hg)
  have hv : v =ᵐ[volume] (fun q : GW.Space => (((‖q‖^2)⁻¹ : ℝ) : ℂ)) := by
    filter_upwards [Lp.coeFn_smul ((a*(g : ℂ))⁻¹) d,hidentity] with q hsmul hd
    change ((a*(g : ℂ))⁻¹ • d) q = _
    rw [hsmul,Pi.smul_apply,smul_eq_mul,hd,Complex.ofReal_div,Complex.ofReal_inv]
    rw [div_eq_mul_inv]
    calc
      (a*(g : ℂ))⁻¹*((g : ℂ)*((‖q‖^2 : ℝ) : ℂ)⁻¹*a) =
          ((a*(g : ℂ))⁻¹*(a*(g : ℂ)))*((‖q‖^2 : ℝ) : ℂ)⁻¹ := by ring
      _ = _ := by rw [inv_mul_cancel₀ hc,one_mul]
  have hi : Integrable (fun q : GW.Space => ‖v q‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)
  have hnorm : (fun q : GW.Space => ‖v q‖^2) =ᵐ[volume]
      (fun q : GW.Space => ‖q‖^(-(4 : ℝ))) := by
    filter_upwards [hv] with q hq
    rw [hq]
    simp only [Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (sq_nonneg ‖q‖))]
    rw [Real.rpow_neg (norm_nonneg q),Real.rpow_ofNat]
    simp only [inv_pow,←pow_mul]
  have hr : Integrable (fun q : GW.Space => ‖q‖^(-(4 : ℝ))) volume := hi.congr hnorm
  exact fourth_power_not_integrableOn_ball 1 zero_lt_one hr.integrableOn

end Froehlich
