import Mathlib.Analysis.Calculus.ContDiff.Basic

set_option autoImplicit false
noncomputable section
namespace Froehlich
variable {D E V : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The ordinary finite-order linear chain rule from regularity at the
actual image point only. The within-set proof uses the same function on
an open neighborhood and its open preimage, without extending it. -/
theorem iteratedFDeriv_comp_linear_at (L : D →L[ℝ] E) (F : E → V)
    (k : ℕ) (x : D) (hF : ContDiffAt ℝ k F (L x)) :
    iteratedFDeriv ℝ k (F ∘ L) x =
      (iteratedFDeriv ℝ k F (L x)).compContinuousLinearMap (fun _ => L) := by
  have hWithin : ContDiffWithinAt ℝ k F Set.univ (L x) := hF.contDiffWithinAt
  have hfinite : (k : WithTop ENat) ≠ ((⊤ : ENat) : WithTop ENat) := by
    exact_mod_cast ENat.natCast_ne_top k
  obtain ⟨S,hS,hx,hOn⟩ := hWithin.contDiffOn' (m := k) le_rfl (fun h => False.elim (hfinite h))
  simp only [Set.insert_eq_of_mem (Set.mem_univ (L x)),Set.univ_inter] at hOn
  have hU : IsOpen (L ⁻¹' S) := hS.preimage L.continuous
  have hi := L.iteratedFDerivWithin_comp_right hOn hS.uniqueDiffOn hU.uniqueDiffOn hx
    (i := k) le_rfl
  rw [iteratedFDerivWithin_of_isOpen k hU hx,
    iteratedFDerivWithin_of_isOpen k hS hx] at hi
  exact hi

theorem iteratedFDeriv_comp_linear_norm_le_at (L : D →L[ℝ] E) (F : E → V)
    (k : ℕ) (x : D) (hF : ContDiffAt ℝ k F (L x)) :
    ‖iteratedFDeriv ℝ k (F ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ k F (L x)‖*‖L‖^k := by
  rw [iteratedFDeriv_comp_linear_at L F k x hF]
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
    ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ k F (L x)) (fun _ : Fin k => L)

end Froehlich
