import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Quantitative remainder calculus from actual first and second norm
derivatives, without assuming continuity of the second derivative. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology Interval
namespace Froehlich
variable {D F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem normDerivative_alongLine (f : D → F) (A : D →L[ℝ] F) (p h : D) (t : ℝ)
    (hf : HasFDerivAt f A (p+t • h)) :
    HasDerivAt (fun s : ℝ => f (p+s • h)) (A h) t := by
  have hline : HasDerivAt (fun s : ℝ => p+s • h) h t := by
    simpa only [one_smul,id_eq] using ((hasDerivAt_id t).smul_const h).const_add p
  exact hf.comp_hasDerivAt t hline

theorem normDerivative_alongLine_apply (DF : D → D →L[ℝ] F)
    (B : D →L[ℝ] D →L[ℝ] F) (p h : D) (t : ℝ)
    (hDF : HasFDerivAt DF B (p+t • h)) :
    HasDerivAt (fun s : ℝ => DF (p+s • h) h) (B h h) t := by
  have hline := normDerivative_alongLine DF B p h t hDF
  have heval : HasFDerivAt (fun A : D →L[ℝ] F => A h) (ContinuousLinearMap.apply ℝ F h)
      (DF (p+t • h)) := (ContinuousLinearMap.apply ℝ F h).hasFDerivAt
  exact heval.comp_hasDerivAt t hline

theorem norm_secondDerivative_direction_bound (B : D →L[ℝ] D →L[ℝ] F) (h : D)
    (L : ℝ) (hB : ‖B‖ ≤ L) : ‖B h h‖ ≤ L * ‖h‖^2 := by
  calc
    ‖B h h‖ ≤ ‖B h‖ * ‖h‖ := (B h).le_opNorm h
    _ ≤ (‖B‖ * ‖h‖) * ‖h‖ := mul_le_mul_of_nonneg_right (B.le_opNorm h) (norm_nonneg h)
    _ = ‖B‖ * ‖h‖^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hB (sq_nonneg ‖h‖)

theorem norm_firstDerivative_segment_increment (DF : D → D →L[ℝ] F)
    (D2 : D → D →L[ℝ] D →L[ℝ] F) (p h : D) (L : ℝ)
    (hDF : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasFDerivAt DF (D2 (p+s • h)) (p+s • h))
    (hL : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖D2 (p+s • h)‖ ≤ L)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖DF (p+t • h) h - DF p h‖ ≤ L * t * ‖h‖^2 := by
  have hm := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun s : ℝ => DF (p+s • h) h)
    (f' := fun s : ℝ => D2 (p+s • h) h h) (a := 0) (b := 1)
    (fun s hs => (normDerivative_alongLine_apply DF (D2 (p+s • h)) p h s (hDF s hs)).hasDerivWithinAt)
    (fun s hs => norm_secondDerivative_direction_bound _ h L (hL s ⟨hs.1,hs.2.le⟩)) t ht
  calc
    _ ≤ (L * ‖h‖^2) * t := by simpa only [zero_smul,add_zero,sub_zero] using hm
    _ = _ := by ring

end Froehlich
