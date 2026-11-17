import Froehlich.Nodes.CA03SingleDifference
import Froehlich.Nodes.CA03Even

set_option autoImplicit false

/-! Local versions of the source finite-difference and even Taylor bounds.
Only the actual convex region or segment is used. In particular these do
not require extending a momentum-dependent kernel beyond its open domain. -/
noncomputable section
namespace Froehlich
variable {D V : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem norm_finiteDifference_le_on_convex (F : D → V) (M : ℝ) (S : Set D)
    (hS : Convex ℝ S) (hF : ∀ y ∈ S, DifferentiableAt ℝ F y)
    (h0 : ∀ y ∈ S, ‖F y‖ ≤ M) (h1 : ∀ y ∈ S, ‖fderiv ℝ F y‖ ≤ M)
    (x h : D) (hx : x ∈ S) (hxh : x+h ∈ S) :
    ‖finiteDifference h F x‖ ≤ 2*M*min ‖h‖ 1 := by
  have hM : 0 ≤ M := (norm_nonneg (F x)).trans (h0 x hx)
  have hsmall : ‖finiteDifference h F x‖ ≤ M*‖h‖ := by
    have hv := Convex.norm_image_sub_le_of_norm_fderiv_le hF h1 hS hx hxh
    simpa only [finiteDifference,add_sub_cancel_left] using hv
  have hlarge : ‖finiteDifference h F x‖ ≤ 2*M :=
    (norm_sub_le _ _).trans (by linarith [h0 (x+h) hxh,h0 x hx])
  by_cases hh : ‖h‖ ≤ 1
  · rw [min_eq_left hh]
    exact hsmall.trans (by nlinarith [norm_nonneg h])
  · rw [min_eq_right (le_of_lt (lt_of_not_ge hh)),mul_one]
    exact hlarge

theorem even_norm_sub_le_quadratic_on_segment (f : D → ℝ)
    (heven : Function.Even f) (h : D) (M : ℝ)
    (hd0 : DifferentiableAt ℝ f 0)
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ f (t • h))
    (hdd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (fderiv ℝ f) (t • h))
    (hM : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ f) (t • h)‖ ≤ M) :
    |f h-f 0| ≤ M*‖h‖^2/2 := by
  have hz := even_fderiv_zero f heven hd0
  have hr := norm_remainder_of_second_fderiv f 0 h M
    (fun t ht => by simpa only [zero_add] using hd t ht)
    (fun t ht => by simpa only [zero_add] using hdd t ht)
    (fun t ht => by simpa only [zero_add] using hM t ht)
  simpa only [zero_add,hz,ContinuousLinearMap.zero_apply,sub_zero,Real.norm_eq_abs] using hr

end Froehlich
