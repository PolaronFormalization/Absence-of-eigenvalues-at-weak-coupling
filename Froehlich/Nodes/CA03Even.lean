import Froehlich.Nodes.CA01GeneralTaylor
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! CA03: an even real C² function has zero derivative at the origin and
therefore the exact source quadratic bound. -/
noncomputable section
namespace Froehlich
variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem even_fderiv_zero (f : D → ℝ) (heven : Function.Even f)
    (hf : DifferentiableAt ℝ f 0) : fderiv ℝ f 0 = 0 := by
  have hd : HasFDerivAt f (fderiv ℝ f 0) (-(0 : D)) := by
    simpa only [neg_zero] using hf.hasFDerivAt
  have hc := hd.comp (0 : D) ((hasFDerivAt_id (0 : D)).neg)
  have he : f ∘ (fun x : D => -x) = f := funext heven
  rw [he] at hc
  have hh := congrArg (fun A : D →L[ℝ] ℝ => A) (hf.hasFDerivAt.unique hc)
  apply ContinuousLinearMap.ext
  intro v
  have hv := congrArg (fun A : D →L[ℝ] ℝ => A v) hh
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.id_apply,map_neg,ContinuousLinearMap.zero_apply] at hv ⊢
  linarith

theorem even_norm_sub_le_quadratic (f : D → ℝ) (heven : Function.Even f)
    (hf : ContDiff ℝ 2 f) (M : ℝ)
    (hM : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) (h : D) :
    |f h-f 0| ≤ M*‖h‖^2/2 := by
  have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hdf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hz := even_fderiv_zero f heven (hdiff 0)
  have hr := norm_remainder_of_second_fderiv f 0 h M
    (fun t ht => hdiff _) (fun t ht => hdf _) (fun t ht => hM _)
  simpa only [zero_add,hz,ContinuousLinearMap.zero_apply,sub_zero,Real.norm_eq_abs] using hr

end Froehlich
