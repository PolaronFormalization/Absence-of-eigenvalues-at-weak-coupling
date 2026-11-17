import Froehlich.Nodes.WE01Operator
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Normed.Operator.Mul

/-! The native Hölder continuous bilinear map supplies multiplication on
ordinary real L-infinity. No new quotient or weighted norm is introduced. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace Froehlich

variable (a : GW.Space → ℝ) (ha : Measurable a) (C : ℝ) (hC : 0 ≤ C)
  (hb : ∀ᵐ q ∂volume, ‖a q‖ ≤ C)

def linftyMultiplierCoefficient : Lp ℝ ⊤ (volume : Measure GW.Space) :=
  (memLp_top_of_bound ha.aestronglyMeasurable C hb).toLp a

theorem linftyMultiplierCoefficient_ae :
    linftyMultiplierCoefficient a ha C hb =ᵐ[volume] a := MemLp.coeFn_toLp _

def nativeLinftyMultiplier :
    Lp ℝ ⊤ (volume : Measure GW.Space) →L[ℝ] Lp ℝ ⊤ (volume : Measure GW.Space) :=
  ((ContinuousLinearMap.mul ℝ ℝ).holderL volume ⊤ ⊤ ⊤)
    (linftyMultiplierCoefficient a ha C hb)

theorem nativeLinftyMultiplier_ae (f : Lp ℝ ⊤ (volume : Measure GW.Space)) :
    nativeLinftyMultiplier a ha C hb f =ᵐ[volume] (fun q => a q*f q) := by
  have h := (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder
    (r := (⊤ : ENNReal)) (linftyMultiplierCoefficient a ha C hb) f
  filter_upwards [h,linftyMultiplierCoefficient_ae a ha C hb] with q hq haQ
  change nativeLinftyMultiplier a ha C hb f q = _
  simpa only [nativeLinftyMultiplier,ContinuousLinearMap.holderL_apply_apply,
    ContinuousLinearMap.mul_apply',haQ] using! hq

include hC in
theorem nativeLinftyMultiplier_norm_le : ‖nativeLinftyMultiplier a ha C hb‖ ≤ C := by
  have hCoeff : ‖linftyMultiplierCoefficient a ha C hb‖ ≤ C := by
    apply linftyReal_norm_le_of_ae_bound _ C hC
    filter_upwards [linftyMultiplierCoefficient_ae a ha C hb,hb] with q hq hbound
    simpa only [hq] using hbound
  have hHolder : ‖((ContinuousLinearMap.mul ℝ ℝ).holderL
      (volume : Measure GW.Space) ⊤ ⊤ ⊤)‖ ≤ 1 :=
    (ContinuousLinearMap.norm_holderL_le (ContinuousLinearMap.mul ℝ ℝ)).trans
      (ContinuousLinearMap.opNorm_mul_le ℝ ℝ)
  exact (((ContinuousLinearMap.mul ℝ ℝ).holderL volume ⊤ ⊤ ⊤).le_opNorm
    (linftyMultiplierCoefficient a ha C hb)).trans
      ((mul_le_mul hHolder hCoeff (norm_nonneg _) zero_le_one).trans_eq (one_mul C))

end Froehlich
