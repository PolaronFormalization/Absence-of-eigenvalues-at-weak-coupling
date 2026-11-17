import Froehlich.Nodes.RS03DerivativesCanonical
import Froehlich.Nodes.RS03DerivativesFiniteNorm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

set_option autoImplicit false

/-! Genuine second Fréchet derivatives and the canonical ordered coordinates. -/
noncomputable section
namespace Froehlich

private theorem rs03_second_partial_eq (F : (Fin 3 → ℝ) → ℝ)
    (hF : ContDiff ℝ 2 F) (q : Fin 3 → ℝ) (i j : Fin 3) :
    coordinatePartial i (coordinatePartial j F) q =
      fderiv ℝ (fderiv ℝ F) q (Pi.single i 1) (Pi.single j 1) := by
  have hd : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (m := 1) (by norm_num)
  have he : coordinatePartial j F = fun p => fderiv ℝ F p (Pi.single j 1) := by
    funext p
    exact coordinatePartial_eq_fderiv j F p (hF.differentiable (by norm_num) p)
  rw [he,coordinatePartial_eq_fderiv i _ q
    ((hd.differentiable (by norm_num) q).clm_apply (differentiableAt_const (Pi.single j 1)))]
  rw [fderiv_clm_apply (hd.differentiable (by norm_num) q) (differentiableAt_const (Pi.single j 1))]
  simp

theorem rs03_hessian_basis_eq_multiPartial (F : (Fin 3 → ℝ) → ℝ)
    (hF : ContDiff ℝ 2 F) (q : Fin 3 → ℝ) (i j : Fin 3) :
    fderiv ℝ (fderiv ℝ F) q (Pi.single i 1) (Pi.single j 1) =
      coordinateMultiPartial ((Pi.single i 1 : Fin 3 → ℕ)+Pi.single j 1) F q := by
  have hord (a b : Fin 3) (hab : a ≤ b) :
      fderiv ℝ (fderiv ℝ F) q (Pi.single a 1) (Pi.single b 1) =
        coordinateMultiPartial ((Pi.single a 1 : Fin 3 → ℕ)+Pi.single b 1) F q := by
    have h := (rs03_second_partial_eq F hF q a b).symm
    fin_cases a <;> fin_cases b <;> norm_num at hab
    all_goals simpa [coordinateMultiPartial,List.ofFn_succ,coordinateBlocksPartial,
      coordinateIterate,Pi.single_apply] using h
  rcases le_total i j with hij | hji
  · exact hord i j hij
  · rw [(hF.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq]
    simpa only [add_comm] using hord j i hji

end Froehlich
