import GW.Model.ModelPowerIntegrals
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.LIntegral

/-! AN00 (`lem:affinemeasure`): change of variables on precisely `GW.Space`
with its retained Euclidean volume. The ball-volume arguments are reused. -/

noncomputable section
open MeasureTheory Metric
open scoped ENNReal Pointwise

namespace Froehlich

theorem space_translation_preserving (b : GW.Space) :
    MeasurePreserving (fun x : GW.Space => x + b) volume volume :=
  measurePreserving_add_right volume b

theorem space_negation_preserving :
    MeasurePreserving (fun x : GW.Space => -x) volume volume :=
  (LinearIsometryEquiv.neg ℝ : GW.Space ≃ₗᵢ[ℝ] GW.Space).measurePreserving

/-- A reflection in any selected coordinate, on the actual Euclidean carrier. -/
def coordinateReflection (i : Fin 3) : GW.Space ≃ₗᵢ[ℝ] GW.Space :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun j : Fin 3 =>
    if j = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

theorem coordinateReflection_apply (i j : Fin 3) (x : GW.Space) :
    coordinateReflection i x j = if j = i then -x j else x j := by
  by_cases h : j = i <;> simp [coordinateReflection, h]

theorem coordinateReflection_preserving (i : Fin 3) :
    MeasurePreserving (coordinateReflection i) volume volume :=
  (coordinateReflection i).measurePreserving

theorem space_dilation_map (a : ℝ) (ha : a ≠ 0) :
    Measure.map (fun x : GW.Space => a • x) volume =
      ENNReal.ofReal ((|a| ^ 3)⁻¹) • volume := by
  simpa [GW.Space, abs_inv, abs_pow] using Measure.map_addHaar_smul
    (volume : Measure GW.Space) ha

theorem space_dilation_measure (a : ℝ) (s : Set GW.Space) :
    volume (a • s) = ENNReal.ofReal (|a| ^ 3) * volume s := by
  simpa [GW.Space, abs_pow] using Measure.addHaar_smul (volume : Measure GW.Space) a s

theorem space_lintegral_dilation (f : GW.Space → ℝ≥0∞) (hf : Measurable f)
    (a : ℝ) (ha : a ≠ 0) :
    (∫⁻ x : GW.Space, f (a • x)) =
      ENNReal.ofReal ((|a| ^ 3)⁻¹) * ∫⁻ y : GW.Space, f y := by
  rw [← lintegral_map hf (measurable_const_smul a), space_dilation_map a ha,
    lintegral_smul_measure, smul_eq_mul]

theorem space_lintegral_affine (f : GW.Space → ℝ≥0∞) (hf : Measurable f)
    (a : ℝ) (ha : a ≠ 0) (b : GW.Space) :
    (∫⁻ x : GW.Space, f (a • x + b)) =
      ENNReal.ofReal ((|a| ^ 3)⁻¹) * ∫⁻ y : GW.Space, f y := by
  rw [space_lintegral_dilation (fun y => f (y + b))
    (hf.comp (measurable_id.add measurable_const)) a ha,
    lintegral_add_right_eq_self]

theorem space_integral_affine (f : GW.Space → ℂ) (a : ℝ) (b : GW.Space) :
    (∫ x : GW.Space, f (a • x + b)) = (|a| ^ 3)⁻¹ • ∫ y : GW.Space, f y := by
  have h := Measure.integral_comp_smul (volume : Measure GW.Space)
    (fun y => f (y + b)) a
  simpa [GW.Space, abs_inv, abs_pow, integral_add_right_eq_self] using h

theorem space_unitBallVolume_pos : 0 < GW.Model.unitBallVolume :=
  GW.Model.unitBallVolume_pos

theorem space_unitBallVolume_finite : volume (ball (0 : GW.Space) 1) < ∞ :=
  measure_ball_lt_top

theorem space_ball_volume (x : GW.Space) (r : ℝ) (hr : 0 < r) :
    volume (ball x r) = ENNReal.ofReal (GW.Model.unitBallVolume * r ^ 3) := by
  rw [Measure.addHaar_ball_center (volume : Measure GW.Space)]
  exact GW.Model.spaceBallVolume r hr

theorem space_sphere_volume (r : ℝ) : volume (sphere (0 : GW.Space) r) = 0 :=
  GW.Model.spaceSphereVolume r

theorem space_closedBall_volume (r : ℝ) (hr : 0 < r) :
    volume (closedBall (0 : GW.Space) r) =
      ENNReal.ofReal (GW.Model.unitBallVolume * r ^ 3) :=
  GW.Model.spaceClosedBallVolume r hr

theorem space_singleton_volume (x : GW.Space) : volume ({x} : Set GW.Space) = 0 :=
  measure_singleton x

end Froehlich
