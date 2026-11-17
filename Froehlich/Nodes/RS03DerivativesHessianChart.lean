import Froehlich.Nodes.RS03DerivativesHessianCoordinates

set_option autoImplicit false

/-! Second Fréchet derivatives under the actual fixed Euclidean chart. -/
noncomputable section
namespace Froehlich

theorem rs03_hessian_linearChart (F : GW.Space → ℝ) (hF : ContDiff ℝ 2 F)
    (L : (Fin 3 → ℝ) →L[ℝ] GW.Space) (q u v : Fin 3 → ℝ) :
    fderiv ℝ (fderiv ℝ (fun t => F (L t))) q u v =
      fderiv ℝ (fderiv ℝ F) (L q) (L u) (L v) := by
  let W : (GW.Space →L[ℝ] ℝ) →L[ℝ] ((Fin 3 → ℝ) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (Fin 3 → ℝ) GW.Space ℝ).flip L
  have hd : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (m := 1) (by norm_num)
  have he : fderiv ℝ (fun t => F (L t)) = fun t => W (fderiv ℝ F (L t)) := by
    funext t
    exact ((hF.differentiable (by norm_num) (L t)).hasFDerivAt.comp t L.hasFDerivAt).fderiv
  have hh := W.hasFDerivAt.comp q
    ((hd.differentiable (by norm_num) (L q)).hasFDerivAt.comp q L.hasFDerivAt)
  rw [he]
  exact congrArg (fun A : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) →L[ℝ] ℝ => A u v) hh.fderiv

end Froehlich
