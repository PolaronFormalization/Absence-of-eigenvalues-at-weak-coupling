import Mathlib.Analysis.Calculus.MeanValue

/-! CA03: one finite difference, with the source small-distance weight.
The native mean-value theorem supplies the derivative estimate; the bound
for large displacements uses two bounded values. Banach-valued targets
allow this same result to start at a derivative map. -/
noncomputable section
namespace Froehlich
variable {D V : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def finiteDifference (h : D) (F : D → V) (x : D) : V := F (x+h)-F x

theorem norm_finiteDifference_le (F : D → V) (M : ℝ)
    (hF : Differentiable ℝ F) (h0 : ∀ x, ‖F x‖ ≤ M)
    (h1 : ∀ x, ‖fderiv ℝ F x‖ ≤ M) (x h : D) :
    ‖finiteDifference h F x‖ ≤ 2*M*min ‖h‖ 1 := by
  have hM : 0 ≤ M := (norm_nonneg (F x)).trans (h0 x)
  have hs : ‖finiteDifference h F x‖ ≤ M*‖h‖ := by
    have hv := Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun y (_ : y ∈ (Set.univ : Set D)) => hF y)
      (fun y (_ : y ∈ (Set.univ : Set D)) => h1 y)
      (convex_univ : Convex ℝ (Set.univ : Set D))
      (Set.mem_univ x) (Set.mem_univ (x+h))
    simpa only [finiteDifference,add_sub_cancel_left] using hv
  have hl : ‖finiteDifference h F x‖ ≤ 2*M := by
    exact (norm_sub_le (F (x+h)) (F x)).trans (by linarith [h0 (x+h),h0 x])
  by_cases hh : ‖h‖ ≤ 1
  · rw [min_eq_left hh]
    exact hs.trans (by nlinarith [norm_nonneg h])
  · rw [min_eq_right (le_of_lt (lt_of_not_ge hh)),mul_one]
    exact hl

end Froehlich
