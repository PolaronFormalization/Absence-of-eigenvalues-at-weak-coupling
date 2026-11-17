import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace Froehlich

/-! Pure numerical preparation for the source's final scalar inequality.
The actual model application still requires the verified WE06 estimates. -/

theorem po03_scalar_criterion (C a r T d : ℝ) (U : ℂ)
    (hC : 1 ≤ C) (ha : 0 ≤ a) (hCa : C*a ≤ 1/4)
    (hr : 0 < r) (hrQuarter : r ≤ 1/4)
    (hU : ‖U‖ ≤ C*a^2) (hT : 0 ≤ T) (hTr : T*r ≤ C*a^2)
    (hd : |d| ≤ C*(r^2+a^2*r)) :
    1+U ≠ 0 ∧ (220/256 : ℝ) ≤ ‖1+U‖^2+T*d := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hCa0 : 0 ≤ C*a := mul_nonneg hC0 ha
  have haQuarter : a ≤ 1/4 := by
    nlinarith only [hCa,mul_nonneg (sub_nonneg.mpr hC) ha]
  have haSq : a^2 ≤ (1/16 : ℝ) := by
    have h := mul_le_mul haQuarter haQuarter ha (by norm_num : (0 : ℝ) ≤ 1/4)
    nlinarith only [h]
  have hCaSq : (C*a)^2 ≤ (1/16 : ℝ) := by
    have h := mul_le_mul hCa hCa hCa0 (by norm_num : (0 : ℝ) ≤ 1/4)
    nlinarith only [h]
  have hCaa : C*a^2 ≤ (1/16 : ℝ) := by
    have h := mul_le_mul hCa haQuarter ha (by norm_num : (0 : ℝ) ≤ 1/4)
    nlinarith only [h]
  have hCSq : C^2*a^2 ≤ (1/16 : ℝ) := by nlinarith only [hCaSq]
  have hFourth : C^2*a^4 ≤ (1/256 : ℝ) := by
    have h := mul_le_mul hCaSq haSq (sq_nonneg a) (by norm_num : (0 : ℝ) ≤ 1/16)
    nlinarith only [h]
  have hUbound : ‖U‖ ≤ (1/16 : ℝ) := hU.trans hCaa
  have hTriangle := norm_add_le (1+U) (-U)
  have hOne : ‖(1+U)+(-U)‖ = (1 : ℝ) := by
    simpa using Complex.norm_natCast 1
  rw [hOne,norm_neg] at hTriangle
  have hLower : (15/16 : ℝ) ≤ ‖1+U‖ := by linarith only [hTriangle,hUbound]
  have hSquare : (225/256 : ℝ) ≤ ‖1+U‖^2 := by
    have h := mul_le_mul hLower hLower (by norm_num : (0 : ℝ) ≤ 15/16) (norm_nonneg (1+U))
    nlinarith only [h]
  have hProduct : T*|d| ≤ C^2*a^2*r+C^2*a^4 := by
    calc
      _ ≤ T*(C*(r^2+a^2*r)) := mul_le_mul_of_nonneg_left hd hT
      _ = (T*r)*(C*(r+a^2)) := by ring
      _ ≤ (C*a^2)*(C*(r+a^2)) := mul_le_mul_of_nonneg_right hTr
        (mul_nonneg hC0 (add_nonneg hr.le (sq_nonneg a)))
      _ = _ := by ring
  have hRadiusTerm : C^2*a^2*r ≤ (1/64 : ℝ) := by
    have h := mul_le_mul hCSq hrQuarter hr.le (by norm_num : (0 : ℝ) ≤ 1/16)
    nlinarith only [h]
  have hSmall : T*|d| ≤ (5/256 : ℝ) := by linarith only [hProduct,hRadiusTerm,hFourth]
  have hSigned : -(T*|d|) ≤ T*d := by
    simpa only [mul_neg] using mul_le_mul_of_nonneg_left (neg_abs_le d) hT
  exact ⟨norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 15/16) hLower),
    by linarith only [hSquare,hSmall,hSigned]⟩

end Froehlich
