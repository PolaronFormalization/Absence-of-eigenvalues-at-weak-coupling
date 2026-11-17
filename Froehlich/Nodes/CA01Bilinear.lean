import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! The source real bilinear product rule is the native bounded-calculus rule. -/
noncomputable section
namespace Froehlich
variable {D V W Z : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem realBilinear_hasFDerivAt (B : V →L[ℝ] W →L[ℝ] Z)
    (F : D → V) (G : D → W) (F' : D →L[ℝ] V) (G' : D →L[ℝ] W) (p : D)
    (hF : HasFDerivAt F F' p) (hG : HasFDerivAt G G' p) :
    HasFDerivAt (fun q => B (F q) (G q))
      (B.precompR D (F p) G' + B.precompL D F' (G p)) p :=
  B.hasFDerivAt_of_bilinear hF hG

theorem realBilinear_derivative_apply (B : V →L[ℝ] W →L[ℝ] Z)
    (v : V) (w : W) (F' : D →L[ℝ] V) (G' : D →L[ℝ] W) (h : D) :
    (B.precompR D v G' + B.precompL D F' w) h = B (F' h) w + B v (G' h) := by
  change B v (G' h) + B (F' h) w = _
  exact add_comm _ _

theorem realBilinear_fderiv_apply (B : V →L[ℝ] W →L[ℝ] Z)
    (F : D → V) (G : D → W) (p h : D)
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p) :
    fderiv ℝ (fun q => B (F q) (G q)) p h =
      B (fderiv ℝ F p h) (G p) + B (F p) (fderiv ℝ G p h) := by
  rw [(realBilinear_hasFDerivAt B F G _ _ p hF.hasFDerivAt hG.hasFDerivAt).fderiv]
  exact realBilinear_derivative_apply B (F p) (G p) _ _ h

theorem realBilinear_hasDerivAt (B : V →L[ℝ] W →L[ℝ] Z)
    (F : ℝ → V) (G : ℝ → W) (v : V) (w : W) (t : ℝ)
    (hF : HasDerivAt F v t) (hG : HasDerivAt G w t) :
    HasDerivAt (fun s => B (F s) (G s)) (B v (G t) + B (F t) w) t := by
  have hd := B.hasDerivAt_of_bilinear (fun _ => hF) (fun _ => hG)
  convert hd using 1
  exact add_comm _ _

end Froehlich
