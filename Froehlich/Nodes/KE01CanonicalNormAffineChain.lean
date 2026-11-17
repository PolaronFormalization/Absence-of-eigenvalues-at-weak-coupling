import Froehlich.Nodes.KE01CanonicalNormLocalChain
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
noncomputable section
namespace Froehlich
variable {D E V : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Translation contributes no derivative factor. Regularity is needed
only at the actual affine image, including when it lies on a closed ball. -/
theorem iteratedFDeriv_comp_affine_at (a : E) (L : D →L[ℝ] E) (F : E → V)
    (k : ℕ) (x : D) (hF : ContDiffAt ℝ k F (a+L x)) :
    iteratedFDeriv ℝ k (fun y => F (a+L y)) x =
      (iteratedFDeriv ℝ k F (a+L x)).compContinuousLinearMap (fun _ => L) := by
  let G : E → V := fun y => F (a+y)
  have hG : ContDiffAt ℝ k G (L x) :=
    hF.comp (L x) (contDiffAt_const.add contDiffAt_id)
  have h := iteratedFDeriv_comp_linear_at L G k x hG
  have ht : iteratedFDeriv ℝ k G (L x) = iteratedFDeriv ℝ k F (a+L x) :=
    iteratedFDeriv_comp_add_left k a (L x)
  rw [ht] at h
  exact h

theorem iteratedFDeriv_comp_affine_norm_le_at (a : E) (L : D →L[ℝ] E)
    (F : E → V) (k : ℕ) (x : D) (hF : ContDiffAt ℝ k F (a+L x)) :
    ‖iteratedFDeriv ℝ k (fun y => F (a+L y)) x‖ ≤
      ‖iteratedFDeriv ℝ k F (a+L x)‖*‖L‖^k := by
  rw [iteratedFDeriv_comp_affine_at a L F k x hF]
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
    ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ k F (a+L x)) (fun _ : Fin k => L)

end Froehlich
