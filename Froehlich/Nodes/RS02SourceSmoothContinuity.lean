import Froehlich.Nodes.RS02SourceSmoothDerivative
import Froehlich.Nodes.CA02WeightedScalarJointBounds

set_option autoImplicit false

/-! Actual L2 source-jet continuity from a uniform local first-difference
bound with the same explicit integrable Gbase vg majorant. -/
noncomputable section
open MeasureTheory Filter
namespace Froehlich

def sourceJetJointCoefficient (r : ℕ) : ℝ :=
  ‖coordinateDerivativeAssembler (E := ℝ) 3‖*scalarDerivativeCoefficientBound (r+1)*
    (1+euclideanChartInverseNorm)

theorem auxiliarySourceJetChartFunction_joint_difference (is : List (Fin 3))
    (g e : ℝ) (he : e ≤ 0) (p q r : Fin 3 → ℝ)
    (hq : q ∈ Metric.closedBall p 1) (hr : r ∈ Metric.closedBall p 1) (k : GW.Space) :
    ‖auxiliarySourceJetChartFunction is g e r k-auxiliarySourceJetChartFunction is g e q k‖ ≤
      (sourceJetJointCoefficient is.length*‖r-q‖)*‖auxiliarySourceJetChartFunction [] g e p k‖ := by
  let p0 := (EuclideanSpace.equiv (Fin 3) ℝ).symm p
  let K : GW.Fock.Coordinates 1 := fun _ => k
  let W := auxiliaryWeight 1 e p0 1 K
  let R := auxiliaryInverseWeightJetChart is 1 e r 1 K-auxiliaryInverseWeightJetChart is 1 e q 1 K
  have hW : 0 < W := zero_lt_one.trans_le (auxiliaryWeight_ge_one 1 1 e p0 he K)
  have hscalar := auxiliaryFixedWeightJetChart_joint_lipschitzOn is 1 1 e p0 he K p q r hq hr
  have hscalar' : |W*R| ≤ sourceJetJointCoefficient is.length*‖r-q‖ := by
    simpa only [p0,W,R,sourceJetJointCoefficient,sub_self,norm_zero,add_zero] using! hscalar
  have hR : |R| ≤ (sourceJetJointCoefficient is.length*‖r-q‖)*W⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ hW).mpr
    have hT : W*|R| ≤ sourceJetJointCoefficient is.length*‖r-q‖ := by
      simpa only [abs_mul,abs_of_pos hW] using hscalar'
    simpa only [mul_comm W] using hT
  have heq : auxiliarySourceJetChartFunction is g e r k-auxiliarySourceJetChartFunction is g e q k =
      (R : ℂ)*(fiberFormFactor g k : ℂ) := by
    simp only [auxiliarySourceJetChartFunction,auxiliarySourceJetFunction,R,
      auxiliaryInverseWeightJetChart,K,Complex.ofReal_sub]
    ring
  have hbase : ‖auxiliarySourceJetChartFunction [] g e p k‖ = W⁻¹*‖(fiberFormFactor g k : ℂ)‖ := by
    change ‖(auxiliaryInverseWeightJet [] 1 e p0 1 K : ℂ)*(fiberFormFactor g k : ℂ)‖ = _
    rw [auxiliaryInverseWeightJet_nil 1 1 e p0 he K,norm_mul,
      Complex.norm_real W⁻¹,Real.norm_eq_abs W⁻¹,abs_of_pos (inv_pos.mpr hW)]
  rw [heq,norm_mul,Complex.norm_real R,Real.norm_eq_abs R,hbase]
  calc
    _ ≤ ((sourceJetJointCoefficient is.length*‖r-q‖)*W⁻¹)*‖(fiberFormFactor g k : ℂ)‖ :=
      mul_le_mul_of_nonneg_right hR (norm_nonneg _)
    _ = _ := by ring

theorem auxiliarySourceJetChartL2_joint_lipschitzOn (is : List (Fin 3))
    (g e : ℝ) (he : e ≤ 0) (p q r : Fin 3 → ℝ)
    (hq : q ∈ Metric.closedBall p 1) (hr : r ∈ Metric.closedBall p 1) :
    ‖auxiliarySourceJetChartL2 is g e r he-auxiliarySourceJetChartL2 is g e q he‖ ≤
      (sourceJetJointCoefficient is.length*‖auxiliarySourceJetChartL2 [] g e p he‖)*‖r-q‖ := by
  calc
    _ ≤ (sourceJetJointCoefficient is.length*‖r-q‖)*‖auxiliarySourceJetChartL2 [] g e p he‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [auxiliarySourceJetChartL2_ae is g e r he,auxiliarySourceJetChartL2_ae is g e q he,
        auxiliarySourceJetChartL2_ae [] g e p he,
        Lp.coeFn_sub (auxiliarySourceJetChartL2 is g e r he) (auxiliarySourceJetChartL2 is g e q he)]
          with k hR hQ hbase hsub
      rw [hsub]
      change ‖auxiliarySourceJetChartL2 is g e r he k-auxiliarySourceJetChartL2 is g e q he k‖ ≤ _
      rw [hR,hQ,hbase]
      exact auxiliarySourceJetChartFunction_joint_difference is g e he p q r hq hr k
    _ = _ := by ring

theorem auxiliarySourceJetChartL2_continuous (is : List (Fin 3)) (g e : ℝ) (he : e ≤ 0) :
    Continuous (fun q : Fin 3 → ℝ => auxiliarySourceJetChartL2 is g e q he) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let C := sourceJetJointCoefficient is.length*‖auxiliarySourceJetChartL2 [] g e p he‖
  have hE : 0 ≤ euclideanChartInverseNorm :=
    (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.opNorm_nonneg
  have hC : 0 ≤ C := mul_nonneg
    (mul_nonneg (mul_nonneg (coordinateDerivativeAssembler (E := ℝ) 3).opNorm_nonneg
      (scalarDerivativeCoefficientBound_nonnegative _)) (by positivity)) (norm_nonneg _)
  have hLip : LipschitzOnWith ⟨C,hC⟩ (fun q => auxiliarySourceJetChartL2 is g e q he)
      (Metric.closedBall p 1) := by
    apply lipschitzOnWith_iff_norm_sub_le.mpr
    intro q hq r hr
    simpa only [NNReal.coe_mk,C] using! auxiliarySourceJetChartL2_joint_lipschitzOn is g e he p r q hr hq
  exact hLip.continuousOn.continuousAt (Metric.closedBall_mem_nhds p (by norm_num))

end Froehlich
